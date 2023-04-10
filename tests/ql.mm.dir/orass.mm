include "ax-a3.mm";

theorem orass(wva: $term$ a, wvb: $term$ b, wvc: $term$ c) {





  do {
    wva;
    wvb;
    wvc;
    ax-a3;
  };

  return $|- ( ( a v b ) v c ) = ( a v ( b v c ) )$;
}
