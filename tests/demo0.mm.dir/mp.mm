
axiom mp(wp: $wff$ P, wq: $wff$ Q) {
  assume min: $|- P$;
  assume maj: $|- ( P -> Q )$;

  return $|- Q$;
}
