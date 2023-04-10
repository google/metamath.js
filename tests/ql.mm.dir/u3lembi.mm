include "i3bi.mm";

theorem u3lembi(wva: $term$ a, wvb: $term$ b) {





  do {
    wva;
    wvb;
    i3bi;
  };

  return $|- ( ( a ->3 b ) ^ ( b ->3 a ) ) = ( a == b )$;
}
