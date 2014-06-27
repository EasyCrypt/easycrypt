/* ---------------------------------------------------------------- */
var Conn = function(s) {
  this.srv_addr = "ws://localhost:8888/";
  this.socket = null;
  this.ws     = ws;

  this.init();
}

/* ---------------------------------------------------------------- */
Conn.prototype.init = function(ws) {
  if (this.socket !== null) this.close();
  this.open(this.srv_addr);
}

Conn.prototype.open = function(addr) {
  function show_header(data) {
    console.log("\n\n======== [" + addr + "] (" + data.type + ")\n");
  }
  function toHTML(data) {
    return data.replace(/&/g, "&amp;").replace(/</g, "&lt;")
               .replace(/>/g, "&gt;").replace(/\n/g, "<br />");
  }

  this.socket = new WebSocket(addr);
  this.results = $("#results");

  this.socket.onopen = function(e) {
    console.log("[+] Opened '" + addr + "'");
    this.results.html("");
  }.bind(this);
  this.socket.onclose = function(e) {
    console.log("[+] Closed '" + addr + "'");
    this.results.text("<offline>");
  }.bind(this);
  this.socket.onmessage = function(e) {
    var data = JSON.parse(e.data);
    switch (data.type) {
    case "step":
      show_header(data);
      this.ws.editor.setStep(data.step);
      break;
    case "notice":
      show_header(data);
      this.results.html(toHTML(data.value));
      break;
    case "error":
      show_header(data);
      break;
    default:
      console.log("ERROR");
    }
  }.bind(this);
  this.socket.onerror = function(e) { console.log("======== [" + addr + "] ERROR\n" + e.data + "========\n"); };
  return this.socket;
}

Conn.prototype.close = function() {
  this.socket.close();
}

Conn.prototype.send = function(data) {
  this.socket.send(data + "\n");
}
