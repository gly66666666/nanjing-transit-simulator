(() => {
  'use strict';

  const recentKey = 'metro_lab_recent_v1';
  const themeKey = 'metro_lab_theme_v1';
  const systemTheme = matchMedia('(prefers-color-scheme: dark)');
  const themes = { system: '跟随系统', light: '浅色', dark: '深色' };
  const byId = id => document.getElementById(id);
  let theme = 'system';
  try { theme = readTheme(localStorage.getItem(themeKey)); } catch {}

  function readTheme(value) {
    return Object.hasOwn(themes, value) ? value : 'system';
  }

  function applyTheme() {
    document.documentElement.dataset.theme = theme === 'system' ? (systemTheme.matches ? 'dark' : 'light') : theme;
  }

  applyTheme();
  systemTheme.addEventListener('change', applyTheme);
  window.addEventListener('storage', event => {
    if (event.key !== themeKey && event.key !== null) return;
    theme = readTheme(event.newValue);
    applyTheme();
    const selector = byId('player-theme');
    if (selector) selector.value = theme;
  });

  function create(tag, className, text) {
    const element = document.createElement(tag);
    if (className) element.className = className;
    if (text) element.textContent = text;
    return element;
  }

  function addButton(parent, text, onClick) {
    const button = create('button', 'player-button', text);
    button.type = 'button';
    button.addEventListener('click', onClick);
    parent.append(button);
    return button;
  }

  function addThemePicker(parent) {
    const label = create('label', 'player-theme');
    const title = create('span', 'player-theme-label', '外观');
    const select = create('select', 'player-button');
    select.id = 'player-theme';
    for (const [value, name] of Object.entries(themes)) select.add(new Option(name, value));
    select.value = theme;
    select.addEventListener('change', () => {
      theme = select.value;
      try { localStorage.setItem(themeKey, theme); } catch {}
      applyTheme();
    });
    label.append(title, select);
    parent.append(label);
  }

  function storeRecent(path) {
    try { localStorage.setItem(recentKey, path); } catch {}
  }

  function recentPath() {
    try { return localStorage.getItem(recentKey); } catch { return null; }
  }

  function lobby(search) {
    addThemePicker(byId('metro-appearance'));
    const normalize = value => value.normalize('NFKC').trim().toLowerCase().replace(/\s+/g, '');
    const sections = [...document.querySelectorAll('main > .grid')].map(grid => ({
      grid,
      heading: grid.previousElementSibling,
      category: grid.classList.contains('region-grid') ? 'region' : 'city',
      cards: [...grid.querySelectorAll('li')].map(item => {
        const link = item.querySelector('a');
        return {
          item, link, title: link.querySelector('strong').textContent,
          terms: normalize(link.textContent + (grid.classList.contains('region-grid') ? '' : grid.previousElementSibling.textContent)),
        };
      }),
    }));
    const toggles = [...document.querySelectorAll('[data-catalog-filter]')];
    let category = 'all';

    function draw() {
      const term = normalize(search.value);
      let count = 0;
      for (const group of sections) {
        let shown = false;
        for (const card of group.cards) {
          const visible = (category === 'all' || category === group.category) && card.terms.includes(term);
          card.item.hidden = !visible;
          shown ||= visible;
          if (visible) count++;
        }
        group.grid.hidden = group.heading.hidden = !shown;
      }
      byId('metro-results-count').textContent = '找到 ' + count + ' 个版本';
      byId('metro-no-results').hidden = count !== 0;
      byId('metro-clear').hidden = !search.value;
    }

    const cards = sections.flatMap(group => group.cards);
    const previous = recentPath();
    const last = cards.find(card => new URL(card.link.href).pathname === previous);
    if (last) {
      const link = byId('last-metro');
      link.href = last.link.href;
      byId('last-metro-name').textContent = last.title;
      const group = byId('last-metro-panel');
      group.hidden = false;
    }
    for (const {link} of cards) link.addEventListener('click', () => storeRecent(new URL(link.href).pathname));

    for (const toggle of toggles) toggle.addEventListener('click', () => {
      category = toggle.dataset.catalogFilter;
      for (const option of toggles) option.setAttribute('aria-pressed', String(option === toggle));
      draw();
    });
    search.addEventListener('input', draw);
    search.addEventListener('keydown', event => {
      if (event.key === 'Escape' && search.value) { search.value = ''; draw(); }
    });
    byId('metro-clear').addEventListener('click', () => {
      search.value = '';
      draw();
      search.focus();
    });
    byId('metro-discovery').hidden = false;
    draw();
  }

  function game(app) {
    const header = app.querySelector('header');
    const aside = app.querySelector('aside');
    const tabs = byId('tabs');
    const map = byId('map');
    if (!header || !aside || !tabs || !map || !window.MetroLab) return;
    storeRecent(location.pathname);

    const controls = create('div', 'player-actions');
    controls.setAttribute('role', 'group');
    controls.setAttribute('aria-label', '游戏工具');
    controls.append(header.querySelector('.city-home'));
    const navHome = controls.querySelector('.city-home');
    navHome.textContent = '城市列表';
    header.insertBefore(controls, tabs);
    aside.id = 'player-sidebar';
    aside.setAttribute('aria-label', '游戏面板');
    tabs.setAttribute('aria-label', '游戏模式');
    const speedRow = byId('speedRow');
    speedRow?.setAttribute('aria-label', '仿真速度');

    const guide = create('dialog', 'player-guide');
    guide.setAttribute('aria-labelledby', 'player-guide-title');
    guide.innerHTML = `<form method="dialog">
      <div class="player-guide-heading"><h2 id="player-guide-title">玩法指南</h2><button class="player-button">关闭</button></div>
      <ol>
        <li><strong>看线网</strong><span>点线路查看站序、发车间隔和运力。拖动地图平移，用滚轮或加减按钮缩放。</span></li>
        <li><strong>做规划</strong><span>新建线路后用「画线」依次点地图上的车站即可铺设：点已接入的站可设为接续点，向前 / 向后延伸或从中间分出支线。改错用「撤销一步」。</span></li>
        <li><strong>跑早高峰</strong><span>进入「模拟」，选好时长和客流强度后开始。结束后查看通勤时间和拥堵站台。</span></li>
        <li><strong>看拓扑图</strong><span>进入「拓扑图」，查看示意站序并导出 PNG。</span></li>
      </ol>
      <p>快捷键：空格键暂停 / 继续仿真，Esc 结束当前画线或关闭弹窗。</p>
      <p>规划进度会自动保存在当前浏览器。也可点击「保存」，下次打开同一版本继续。</p>
    </form>`;
    document.body.append(guide);

    const toggle = addButton(controls, '收起面板', () => setPanel(!collapsed));
    toggle.setAttribute('aria-controls', aside.id);
    addButton(controls, '帮助', () => guide.showModal());
    const saveButton = addButton(controls, '保存', () => {
      const started = Date.now();
      saveNow(true);
      const saved = loadSave()?.t >= started;
      const message = saved ? '规划已保存在当前浏览器' : '当前浏览器未能写入存档';
      saveStatus.textContent = '';
      requestAnimationFrame(() => { saveStatus.textContent = message; });
      toast(message);
    });
    saveButton.setAttribute('aria-label', '保存规划');
    const saveStatus = create('span', 'player-sr-only');
    saveStatus.setAttribute('role', 'status');
    controls.append(saveStatus);
    addThemePicker(controls);

    const names = {
      zoomIn:'放大地图', zoomOut:'缩小地图', zoomFit:'适配全图',
      dtHeadway:'发车间隔', dtSpeed:'旅行速度', dtCap:'编组定员',
      simDur:'仿真时长', simDem:'客流强度', editLineSel:'正在编辑的线路',
    };
    for (const [id,label] of Object.entries(names)) byId(id)?.setAttribute('aria-label', label);
    map.setAttribute('aria-label', '地铁线网地图');

    let collapsed = matchMedia('(max-width: 720px)').matches;
    let currentMode = '';
    function setPanel(value) {
      collapsed = value;
      app.classList.toggle('player-panel-closed', value);
      toggle.textContent = value ? '展开面板' : '收起面板';
      toggle.setAttribute('aria-expanded', String(!value));
    }

    function syncSelection() {
      for (const button of document.querySelectorAll('#tabs button[data-mode], #speedRow button[data-speed]')) {
        button.setAttribute('aria-pressed', String(button.classList.contains('active')));
      }
      const mode = tabs.querySelector('button.active')?.dataset.mode;
      if (!mode || mode === currentMode) return;
      app.dataset.playerMode = mode;
      toggle.hidden = mode === 'chart';
      if (mode === 'sim' || mode === 'edit') setPanel(false);
      aside.scrollTop = 0;
      currentMode = mode;
    }

    // 原引擎更新活动标签，本层同步面板和无障碍状态。
    const observer = new MutationObserver(syncSelection);
    const observerOptions = { subtree:true, attributes:true, attributeFilter:['class'] };
    observer.observe(tabs, observerOptions);
    if (speedRow) observer.observe(speedRow, observerOptions);
    function keepControlKeys(event) {
      if (event.key === ' ' || event.key === 'Escape') event.stopPropagation();
    }
    controls.addEventListener('keydown', keepControlKeys);
    guide.addEventListener('keydown', keepControlKeys);

    setPanel(collapsed);
    syncSelection();
    app.classList.add('player-ready');
    const wrapper = map.parentElement;
    let lastWidth = wrapper.clientWidth;
    let lastHeight = wrapper.clientHeight;
    resizeCanvas();
    window.MetroLab.fitCity();
    new ResizeObserver(() => {
      if (wrapper.clientWidth === lastWidth && wrapper.clientHeight === lastHeight) return;
      lastWidth = wrapper.clientWidth;
      lastHeight = wrapper.clientHeight;
      resizeCanvas();
      if (currentMode === 'chart') window.MetroLab.fitChart();
    }).observe(wrapper);
  }

  // 在引擎的 document 初始化之后绑定游戏工具。
  window.addEventListener('DOMContentLoaded', () => {
    const search = byId('metro-search');
    const app = byId('app');
    if (search) lobby(search);
    else if (app) game(app);
  });
})();
