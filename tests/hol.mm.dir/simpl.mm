include "ax-simpl.mm";

theorem simpl(tr: $term$ R, ts: $term$ S) {
  assume ax-simpl.1: $|- R : bool$;
  assume ax-simpl.2: $|- S : bool$;





  do {
    tr;
    ts;
    ax-simpl.1;
    ax-simpl.2;
    ax-simpl;
  };

  return $|- ( R , S ) |= R$;
}
