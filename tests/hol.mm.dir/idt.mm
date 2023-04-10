
theorem idt(hal: $type$ al, ta: $term$ A) {
  assume idt.1: $|- A : al$;





  do {
    idt.1;
  };

  return $|- A : al$;
}
