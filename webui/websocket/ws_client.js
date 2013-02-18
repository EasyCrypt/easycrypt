"use strict";
    // Initialize everything when the window finishes loading
    window.addEventListener("load", function(event) {
      var status = document.getElementById("status");
      var url = document.getElementById("url");
      var open = document.getElementById("open");
      var close = document.getElementById("close");
      var send = document.getElementById("send");
      var text = document.getElementById("text");
      var message = document.getElementById("message");
      var socket;

      status.textContent = "Not Connected";
      url.value = "ws://localhost:8080";
      close.disabled = true;
      send.disabled = true;

      // Create a new connection when the Connect button is clicked
      open.addEventListener("click", function(event) {
        open.disabled = true;
        socket = new WebSocket(url.value, "echo-protocol");

        socket.onopen = function(event) {
          close.disabled = false;
          send.disabled = false;
          status.textContent = "Connected";
        };

        // Display messages received from the server
        socket.onmessage = function(event) {
        /*	try{
        		var json = JSON.parse(event.data);
        	} catch (e) {
        		console.log('This doesn\'t look like a valid JSON: ', event.data);
        		return;
        		}*/
          message.textContent = "Server Says: " + event.data;
        };

        // Display any errors that occur
        socket.onerror = function(event) {
          message.textContent = "Error: " + event;
        };

        socket.onclose = function(event) {
          open.disabled = false;
          status.textContent = "Not Connected";
        };
      });

      // Close the connection when the Disconnect button is clicked
      close.addEventListener("click", function(event) {
        close.disabled = true;
        send.disabled = true;
        message.textContent = "";
        socket.close();
      });

      // Send text to the server when the Send button is clicked
      send.addEventListener("click", function(event) {
        socket.send(text.value);
        text.value = "";
      });
    });