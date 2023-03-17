include "ax-simpr.mm"

theorem simpr
  let tr: term R
  let ts: term S
  assume ax-simpl.1: |- R : bool
  assume ax-simpl.2: |- S : bool


  assert |- ( R , S ) |= S

  proof
    tr
    ts
    ax-simpl.1
    ax-simpl.2
    ax-simpr
end
