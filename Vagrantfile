Vagrant.configure(2) do |config|

  project_name = File.dirname(__FILE__).split("/").last

  config.vm.provider "virtualbox" do |vb|
    vb.memory = 6144 # set VM memory to 6GB
  end
  config.vm.synced_folder ".", "/home/vagrant/#{project_name}"

  config.vm.define :ubuntu do |ubuntu_config|
    ubuntu_config.vm.box = "ubuntu/wily64"
  end

  config.vm.provision "shell", binary: true, privileged: false, inline: <<-SHELL
    echo "Installing dependencies from Ubuntu packages."
    sudo DEBIAN_FRONTEND=noninteractive apt-get install -qq -yy m4 opam libgmp-dev libpcre3-dev pkg-config emacs24
    echo "Initializing opam."
    opam init -q -a --compiler=4.02.1
    eval `opam config env`
    opam repository add easycrypt git://github.com/EasyCrypt/opam.git
    opam update
#    echo "Installing EasyCrypt and dependencies from OPAM packages."
#    opam install -q easycrypt ec-provers ec-proofgeneral
#    why3 config --detect -C /home/vagrant/.why3.conf
    echo "Installing EasyCrypt dependencies from OPAM packages."
    opam install -q ec-toolchain.20150923 ec-provers
    why3 config --detect -C /home/vagrant/.why3.conf
    cd #{project_name}
    echo "Building EasyCrypt."
    make && make -C proofgeneral local
    echo "Now use vagrant ssh -- -X and make pg"
  SHELL

end
