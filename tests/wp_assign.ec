game wp_assign1 = {

  var n1, n2 : int

  fun Main () : bool = {
    n1 = 1;
    n2 = 2;
    return true;
  }

  fun Main2 () : bool = {
    n2 = 2;
    n1 = 1;
    return true;
  }

}.     

equiv foo : wp_assign1.Main ~ wp_assign1.Main : true ==> ={n1,n2} by auto.
