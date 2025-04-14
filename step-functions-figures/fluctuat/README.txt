## Prerequisites
---
- You need a fluctuat license (fluctuat.lic) for this to work.
  Contact cea list for a license contact information can be found
  at https://www.lix.polytechnique.fr/Labo/Sylvie.Putot/fluctuat.html

- If on a mac get xQuartz from https://www.xquartz.org
- Ensure that the "Allow connections from network clients" option is
  enabled. You can find it in the settings under "Security"

## Instructions
---
These instructions were run on a macbook pro with an M3 chip.

1. ensure that your display variable is set, e.g. 
     `export DISPLAY=192.168.137.23:0`
2. Allow connections from docker `xhost +local:docker`
3. Build the docker container: `make build` 
4. Run the docker container: `make run`
5. You should be able to run `fluctuat` in the container and have the
   UI open in a window.
