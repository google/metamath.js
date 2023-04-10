include "ax-a2.mm";

theorem orcom(wva: $term$ a, wvb: $term$ b) {





  do {
    wva;
    wvb;
    ax-a2;
  };

  return $|-$ $( a v b ) = ( b v a )$;
}
