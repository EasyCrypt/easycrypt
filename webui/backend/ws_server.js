#!/usr/bin/env node
var WebSocketServer = require('../lib/WebSocketServer');
var http = require('http');

// list of currently connected clients (users)
var clients = [ ];

var server = http.createServer(function(request, response) {
    console.log((new Date()) + ' Received request for ' + request.origin);
    response.writeHead(404);
    response.end();
});
server.listen(8080, function() {
    console.log((new Date()) + ' Server is listening on port 8080');
});

wsServer = new WebSocketServer({
    httpServer: server,
    // You should not use autoAcceptConnections for production
    // applications, as it defeats all standard cross-origin protection
    // facilities built into the protocol and the browser.  You should
    // *always* verify the connection's origin and decide whether or not
    // to accept it.
    autoAcceptConnections: false
});

function originIsAllowed(origin) {
  // put logic here to detect whether the specified origin is allowed.
  return true;
}

function analyzeS(statement) {
	  // function to analyze the statement sent by the user
	try{
		var json = JSON.parse(statement);
	} catch (e) {
		console.log('This doesn\'t look like a valid JSON: ', json);
		return;
		}
	//NOW just to try the error
	if (json.end.contents.match("axim") == "axim") {
		var error = JSON.stringify({     mode : "error",
										  end : json.end,
									start_err : "2", 
									  end_err : "6",
									  message : "We have an error!"});
		// broadcast message to all connected clients
        for (var i=0; i < clients.length; i++) {
            clients[i].send(error);
        }
	}
	else {
		// broadcast message to all connected clients
        for (var i=0; i < clients.length; i++) {
            clients[i].send(statement);
        }
	}
	
	}

wsServer.on('request', function(request) {
    if (!originIsAllowed(request.origin)) {
      // Make sure we only accept requests from an allowed origin
      request.reject();
      console.log((new Date()) + ' Connection from origin ' + request.origin + ' rejected.');
      return;
    }

    var connection = request.accept('echo-protocol', request.origin);
    // we need to know client index to remove them on 'close' event
    var index = clients.push(connection) - 1;
    console.log((new Date()) + ' Connection accepted.'); 

    
    connection.on('message', function(message) {
    	try{
    		var json = JSON.parse(message.utf8Data);
    	} catch (e) {
    		console.log('This doesn\'t look like a valid JSON: ', json);
    		return;
    		}
        if (json.mode == "forward") {
        	analyzeS(message.utf8Data);
        	console.log('Received Message: ' + json.end.contents);
        }
        	
        else if (json.mode == "undo") {
        	for (var i=0; i < clients.length; i++) {
                clients[i].send(JSON.stringify({ mode : "undo", data: "Undo operation - OK"}));
            }
            console.log('Undo operation');
        }
    });
    
    connection.on('close', function(reasonCode, description) {
        console.log((new Date()) + ' Peer ' + connection.remoteAddress + ' disconnected.');
        // remove user from the list of connected clients
        clients.splice(index, 1);
    });
});