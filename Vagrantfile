Vagrant.configure(2) do |config|

  project_name = File.dirname(__FILE__).split("/").last

  config.vm.provider "virtualbox" do |vb|
    vb.memory = 6144 # set VM memory to 6GB
  end

  config.vm.synced_folder ".", "/home/vagrant/#{project_name}"

  config.vm.define :ubuntu do |ubuntu_config|
    ubuntu_config.vm.box = "ubuntu/wily64"
  end

  config.vm.provision "shell", binary: true, privileged: false do |s|
    s.path = "scripts/vagrant/post-installation.sh"
    s.args = ["#{project_name}"]
  end
end
