import argparse
import os
import time
import threading
from playwright.sync_api import sync_playwright

def parse_messages(names_arg):
    if names_arg.endswith('.txt'):
        if not os.path.exists(names_arg):
            print(f"File {names_arg} not found.")
            return []
        with open(names_arg, 'r', encoding='utf-8') as f:
            content = f.read().strip()
    else:
        content = names_arg.strip()

    # Sirf & aur 'and' se hi split hoga
    content = content.replace(' and ', '&')
    messages = [msg.strip() for msg in content.split('&') if msg.strip()]
    return messages

def sender(tab_id, args, messages, headless, storage_path):
    with sync_playwright() as p:
        browser = p.chromium.launch(headless=headless)
        context = browser.new_context(storage_state=storage_path)
        page = context.new_page()
        dm_selector = 'div[role="textbox"][aria-label="Message"]'
        try:
            page.goto(args.thread_url, timeout=60000)
            page.wait_for_selector(dm_selector, timeout=30000)
            print(f"Tab {tab_id} ready, starting infinite message loop.")
            while True:
                for msg in messages:
                    try:
                        if not page.locator(dm_selector).is_visible():
                            print(f"Tab {tab_id} Selector not visible, skipping '{msg}'")
                            time.sleep(0.3)
                            continue
                        page.click(dm_selector)
                        page.fill(dm_selector, msg)
                        page.press(dm_selector, 'Enter')
                        print(f"Tab {tab_id} Sending: {msg}")
                        time.sleep(0.3)
                    except Exception as e:
                        print(f"Tab {tab_id} Error sending message '{msg}': {e}")
                        time.sleep(0.3)
        except Exception as e:
            print(f"Tab {tab_id} Unexpected error: {e}")
        finally:
            browser.close()

def main():
    parser = argparse.ArgumentParser(description="Instagram DM Auto Sender using Playwright")
    parser.add_argument('--username', required=False, help='Instagram username')
    parser.add_argument('--password', required=False, help='Instagram password')
    parser.add_argument('--thread-url', required=True, help='Full Instagram direct thread URL')
    parser.add_argument('--names', required=True, help='Comma-separated, &-separated, or "and"-separated messages list (e.g., "Example 1& Example 2") or path to .txt file')
    parser.add_argument('--headless', default='true', help='true/false (optional, default true)')
    parser.add_argument('--storage-state', required=True, help='Path to JSON file to save/load login state')
    parser.add_argument('--tabs', type=int, default=1, help='Number of parallel tabs (1-3, default 1)')

    args = parser.parse_args()

    headless = args.headless.lower() == 'true'
    storage_path = args.storage_state

    do_login = not os.path.exists(storage_path)
    if do_login:
        if not args.username or not args.password:
            print("Username and password required for login.")
            return
        with sync_playwright() as p:
            browser = p.chromium.launch(headless=headless)
            context = browser.new_context()
            page = context.new_page()
            try:
                print("Logging in...")
                page.goto("https://www.instagram.com/", timeout=60000)
                page.wait_for_selector('input[name="username"]', timeout=30000)
                page.fill('input[name="username"]', args.username)
                page.fill('input[name="password"]', args.password)
                page.click('button[type="submit"]')
                page.wait_for_url("https://www.instagram.com/", timeout=60000)
                print("Login successful, saving storage state.")
                context.storage_state(path=storage_path)
            except Exception as e:
                print(f"Login error: {e}")
            finally:
                browser.close()
    else:
        print("Loaded storage state, skipping login.")

    messages = parse_messages(args.names)
    if not messages:
        print("No messages provided.")
        return

    tabs = min(max(args.tabs, 1), 3)
    threads = []
    for i in range(tabs):
        t = threading.Thread(target=sender, args=(i+1, args, messages, headless, storage_path))
        t.daemon = True
        t.start()
        threads.append(t)

    print(f"Starting {tabs} tabs infinite message loop. Press Ctrl+C to stop.")
    try:
        for t in threads:
            t.join()
    except KeyboardInterrupt:
        print("Stopping tabs...")

if __name__ == "__main__":
    main()