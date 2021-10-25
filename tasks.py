import os
from pathlib import Path
import http.server
import socketserver
from invoke import run, task

ROOT = Path(__file__).parent

@task
def pdf(ctx):
    """Builds the pdf version in the print folder"""
    cwd = os.getcwd()
    os.chdir(ROOT)
    run('mkdir -p print && cd doc && xelatex -output-directory=../print blueprint.tex')
    run('cd print && bibtex blueprint.aux', env={'BIBINPUTS': '../doc'})
    run('cd doc && xelatex -output-directory=../print blueprint.tex')
    run('cd doc && xelatex -output-directory=../print blueprint.tex')
    os.chdir(cwd)

@task
def qpdf(ctx):
    """Quick pdf (don't try to rebuild references)"""
    cwd = os.getcwd()
    os.chdir(ROOT)
    run('mkdir -p print && cd doc && xelatex -output-directory=../print blueprint.tex')
    os.chdir(cwd)

@task
def decls(ctx):
    from mathlibtools.lib import LeanProject

    """Rebuild the Lean declarations database"""
    proj = LeanProject.from_path((ROOT/'project').resolve())
    proj.build()
    proj.pickle_decls(ROOT/'project'/'decls.pickle')

@task(decls, pdf)
def web(ctx):
    """Builds the web version in the web folder"""
    cwd = os.getcwd()
    os.chdir(ROOT)
    run('cp print/blueprint.bbl doc/web.bbl')
    os.chdir(ROOT/'doc')
    run('plastex -c plastex.cfg web.tex')
    os.chdir(cwd)

@task
def qweb(ctx):
    """Quick web (don't try to rebuild references or links to Lean code)"""
    cwd = os.getcwd()
    os.chdir(ROOT/'doc')
    run('plastex -c plastex.cfg web.tex')
    os.chdir(cwd)

@task
def serve(ctx):
    """Locally serve the web version (useful to see the dep graph)"""
    cwd = os.getcwd()
    os.chdir(ROOT/'web')
    Handler = http.server.SimpleHTTPRequestHandler
    httpd = socketserver.TCPServer(("", 8000), Handler)
    httpd.serve_forever()
    os.chdir(cwd)
