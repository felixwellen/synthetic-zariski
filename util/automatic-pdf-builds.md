Automatic pdf builds
====================
Currently, all the drafts are build hourly on felix-cherubini.de. README.md contains links to all the builds.

Build scripts
-------------
Components:

- A podman (Redhat's variant of docker) container for building pdfs defined by this ```Containerfile```:
  ```dockerfile
  FROM fedora:latest
  
  RUN dnf update -y
  RUN dnf install -y texlive texlive-latex texlive-collection-fontsrecommended
  RUN dnf install -y git
  
  RUN dnf install -y latexmk texlive-stmaryrd texlive-amsmath texlive-babel texlive-biblatex texlive-booktabs texlive-cleveref texlive-enumitem texlive-hyperref texlive-latex-fonts texlive-pgf texlive-thmtools texlive-tipa texlive-tikz-cd
  
  ADD build-sag.sh /build-sag.sh
  ```
  where ```build-sag.sh``` is:
  ```bash
  #!/usr/bin/env bash
  # clone from repo and build the synthetic algebraic geometry drafts
  
  # Check if there are at least two arguments
  if [ "$#" -lt 2 ]; then
      echo "Usage: $0 folder1 [folder2 ...]"
      echo "where folderN is a subfolder of the synthetic-zariski repo"
      echo "script assumes we are in a container"
      exit 1
  fi
  
  mkdir /out 
  
  # Checkout only the latest status
  git clone --depth 1 https://github.com/felixwellen/synthetic-zariski.git
  
  for folder in "$@"; do
      echo "building $folder"
      cd /synthetic-zariski/$folder
      latexmk -pdf main.tex
      cp main.pdf /out/$folder.pdf
  done
  ```
  The (podman) image needs to be built once with:
  ```bash
  podman build -t sag-latex .
  ```
- A systemd  timer (```/etc/systemd/user/sag-latex.timer```) 
  ```systemd
  [Unit]
  Description=Timer for building and publishing SAG pdfs
  
  [Timer]
  OnCalendar=hourly
  
  [Install]
  WantedBy=timers.target
  ```
  and service (```/etc/systemd/user/sag-latex.service```)
  ```systemd
  [Unit]
  Description=Fetch latest latex-sources of the SAG github repo, build and publish the pdfs
  
  [Service]
  Type=oneshot
  ExecStart=/home/felix/build-and-publish-sag.sh
  ```
  where the refernced script is:
  ```bash
  #!/usr/bin/env bash
  # call build container for SAG pdfs and publish
  
  # sub folders in the synthetic-zariski repo that contain some latex to be build
  folders=("A1-homotopy" "cech" "condensed" "condensed-cohomology" "condensed-sheaves" "condensed-summary" "diffgeo" "elliptic" "exercises" "finite" "foundations" "proper" "random-facts" "sheaves" "stacks" "topology" "projective")
  
  # build using the podman container,
  # delete possibly existing containers with the name before that
  podman rm -i sag-latex-latest
  podman run --name sag-latex-latest -t localhost/sag-latex:latest /build-sag.sh ${folders[@]}
  
  # publish
  container_id=$(podman ps -aqf "name=sag-latex-latest")
  
  for folder in ${folders[@]}; do
      podman cp $container_id:/out/$folder.pdf /var/website-html/
  done
  
  # legacy (want to keep some links working)
  # old abreviation for internal algebraic geometry
  podman cp $container_id:/out/foundations.pdf /var/website-html/iag.pdf
  # a typo...
  podman cp $container_id:/out/cech.pdf /var/website-html/chech.pdf      
  podman cp $container_id:/out/random-facts.pdf /var/website-html/random.pdf      
  ```
  The timer is activated by:
  ```bash
  systemctl --user enable sag-latex.timer 
  systemctl --user start sag-latex.timer 
  ```

Webhooks
--------
Under Settings/Webhooks on the github page of this repo, I created a webhook which sends a post 'https://felix-cherubini.de/synthetic-zariski-push'. The plan is that this section in the ```nginx.conf``` on ```felix-cherubini.de```:
```
        location /synthetic-zariski-push {
             proxy_pass http://127.0.0.1:1728;
             proxy_pass_request_body off;
             proxy_pass_request_headers off;
        }
```
proxies the post to a http server defined by this python script:
```python
import http.server                                                                
import socketserver                                                               
import subprocess                                                                 
                                                                                  
class RequestHandler(http.server.SimpleHTTPRequestHandler):                       
    def do_POST(self):                                                            
        # Start systemd user service                                              
        subprocess.run(['systemctl', '--user', 'start', 'sag-latex'])           
        self.send_response(200)                                                   
                                                                                  
with socketserver.TCPServer(('127.0.0.1', 1728), RequestHandler) as httpd:        
    print('Server started on http://127.0.0.1:1728')                              
    httpd.serve_forever()
```
which starts the service that builds all drafts. ```restart``` would be great when multiple posts come in a short time, but unfortunately, that messes up podman in a wicked way. So currently the building is started event based *and* time based.
