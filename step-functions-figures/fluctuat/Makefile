build:
	sudo docker build --platform linux/amd64 -t fluctuat -f Dockerfile .

run:
	docker run --name fluct --rm -it -e DISPLAY=host.docker.internal:0 -v /tmp/.X11-unix:/tmp/.X11-unix fluctuat bash
