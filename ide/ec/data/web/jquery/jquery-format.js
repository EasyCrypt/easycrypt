/*
 * Extracted from jQuery Validation Plugin 1.11.0pre
 *
 * http://bassistance.de/jquery-plugins/jquery-plugin-validation/
 * http://docs.jquery.com/Plugins/Validation
 *
 * Copyright 2013 Jörn Zaefferer
 * Released under the MIT license:
 *   http://www.opensource.org/licenses/mit-license.php
 */

jQuery.extend({
    format: function(source, params) {
      if (arguments.length === 1) {
          return function() {
              var args = $.makeArray(arguments);
              args.unshift(source);
              return $.validator.format.apply( this, args );
          };
      }
      if (arguments.length > 2 && params.constructor !== Array) {
          params = $.makeArray(arguments).slice(1);
      }
      if (params.constructor !== Array) {
          params = [ params ];
      }
      $.each(params, function(i, n) {
          source = source.replace(new RegExp("\\{" + i + "\\}", "g"), function() {
              return n;
          });
      });
      return source;
    }
});
