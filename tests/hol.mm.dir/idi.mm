
theorem idi(ta: $term$ A, tr: $term$ R) {
  assume idi.1: $|- R |= A$;





  do {
    idi.1;
  };

  return $|-$ $R |= A$;
}
