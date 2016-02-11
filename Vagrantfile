Vagrant.configure(2) do |config|

  project_name = File.dirname(__FILE__).split("/").last

  config.vm.provider "virtualbox" do |vb|
    vb.memory = 6144 # set VM memory to 6GB
  end

  config.vm.define "easycrypt", primary: true do |config|
    config.vm.box = "ubuntu/wily64"
    config.vm.hostname = "ec-vagrant"
    config.vm.synced_folder ".", "/home/vagrant/#{project_name}"

    config.vm.provision "shell", binary: true, privileged: false do |s|
      s.path = "scripts/vagrant/post-installation.sh"
      s.args = ["#{project_name}", "shared"]
    end
  end

  config.vm.define "easycrypt-gui", autostart: false do |config|
    config.vm.box     = "easycrypt"
    config.vm.box_url = "https://www.easycrypt.info/vagrant/easycrypt-base.box"

    config.vm.hostname  = "easycrypt"
    config.ssh.username = "easycrypt"
    config.ssh.password = "easycrypt"

    config.vm.provider "virtualbox" do |vb|
      vb.customize ["modifyvm", :id, "--vram", "128"]
      vb.customize ["modifyvm", :id, "--accelerate3d", "off"]
      vb.customize ["modifyvm", :id, "--clipboard", "bidirectional"]
    end

    config.vm.provision "shell", binary: true, privileged: false do |s|
      s.path = "scripts/vagrant/post-installation.sh"
      s.args = ["#{project_name}", "cloned"]
    end
  end
end
