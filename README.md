# Price Discovery Event / Liquidity Bootstrapping Smart Contracts  

Open-source contracts for conducting permissionless price discovery / liquidity bootstrapping events to launch your token in a fair, tamperproof manner. 

The Discovery Smart Contracts were developed through the collaborative efforts of Anastasia Labs and Ikigai Technologies.

https://anastasialabs.com/

https://ikigaitech.org

https://beta.grabbit.market

https://cardano.ideascale.com/c/idea/103903

# Set up nix config 
Put the following lines in your nix configuration file (usually located at /etc/nix/nix.conf)

extra-experimental-features = nix-command flakes ca-derivations
extra-trusted-substituters = https://cache.iog.io https://cache.nixos.org/ https://public-plutonomicon.cachix.org https://cache.zw3rk
extra-trusted-public-keys = cache.iog.io:f/Ea+s+dFdN+3Y/G+FDgSq+a5NEWhJGzdjvKNGv0/EQ= cache.nixos.org-1:6NCHdD59X431o0gWypbMrAURkbJ16ZPMQFGspcDShjY= public-plutonomicon.cachix.org-1:3AKJMhCLn32gri1drGuaZmFrmnue+KkKrhhubQk/CWc=

# Installation 
After setting up nix config, restart your computer or VM. 
Then run:
    nix develop 

# License
See the [LICENSE](LICENSE) file for license rights and limitations (MIT).