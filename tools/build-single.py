#!/usr/bin/env python3
"""Собирает всю игру в один файл dist/pyatyi-postulat.html (скрипты и иконка внутри).
Запуск: python3 tools/build-single.py"""
import base64,os,re
R=os.path.dirname(os.path.dirname(os.path.abspath(__file__)));D=os.path.join(R,'dist');os.makedirs(D,exist_ok=True)
s=open(os.path.join(R,'index.html'),encoding='utf-8').read()
def inl(m):
    js=open(os.path.join(R,m.group(1)),encoding='utf-8').read().replace('</script','<\\/script')
    return '<script>\n'+js+'\n</script>'
s=re.sub(r'<script src="([\w.]+)"></script>',inl,s)
ico=base64.b64encode(open(os.path.join(R,'icons/icon.svg'),'rb').read()).decode()
s=s.replace('<link rel="manifest" href="manifest.webmanifest">','').replace('href="icons/icon.svg"','href="data:image/svg+xml;base64,'+ico+'"')
s=re.sub(r'<link rel="apple-touch-icon"[^>]*>','',s)
open(os.path.join(D,'pyatyi-postulat.html'),'w',encoding='utf-8').write(s)
print('dist/pyatyi-postulat.html',len(s.encode())//1024,'КБ')
