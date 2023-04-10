include "biid.mm";

theorem ska1(wva: $term$ a) {





  do {
    wva;
    biid;
  };

  return $|- ( a == a ) = 1$;
}
