include "ax-simpl.mm"

theorem simpl
  param tr: term R
  param ts: term S
  assume ax-simpl.1: |- R : bool
  assume ax-simpl.2: |- S : bool


  assert |- ( R , S ) |= R

  proof
    tr
    ts
    ax-simpl.1
    ax-simpl.2
    ax-simpl
end
