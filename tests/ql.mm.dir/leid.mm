include "id.mm";
include "bile.mm";

theorem leid(wva: $term$ a) {





  do {
    wva;
    wva;
    wva;
    id;
    bile;
  };

  return $|- a =< a$;
}
