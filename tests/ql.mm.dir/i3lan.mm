include "wa.mm";
include "i3ran.mm";
include "ancom.mm";
include "i33tr1.mm";

theorem i3lan(wva: $term$ a, wvb: $term$ b, wvc: $term$ c) {
  assume i3lan.1: $|- ( a ->3 b ) = 1$;





  do {
    wva;
    wvc;
    wa;
    wvb;
    wvc;
    wa;
    wvc;
    wva;
    wa;
    wvc;
    wvb;
    wa;
    wva;
    wvb;
    wvc;
    i3lan.1;
    i3ran;
    wvc;
    wva;
    ancom;
    wvc;
    wvb;
    ancom;
    i33tr1;
  };

  return $|- ( ( c ^ a ) ->3 ( c ^ b ) ) = 1$;
}
