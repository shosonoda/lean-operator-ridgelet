from conftest import selected_browser_types


def test_empty_playwright_browser_option_uses_default_browser():
    assert selected_browser_types([]) == {"chromium"}


def test_missing_browser_option_uses_default_browser():
    assert selected_browser_types(None) == {"chromium"}
    assert selected_browser_types("") == {"chromium"}


def test_explicit_browser_selection_is_preserved():
    assert selected_browser_types("firefox") == {"firefox"}
    assert selected_browser_types(["chromium", "firefox"]) == {"chromium", "firefox"}
