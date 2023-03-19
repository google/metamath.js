include "kt.mm"
include "alrimiv.mm"

theorem axgen
  let hal: type al
  let vx: var x
  let tr: term R
  assume axgen.1: |- T. |= R

  disjoint al x
  assert |- T. |= ( ! \ x : al . R )

  proof
    hal
    vx
    tr
    kt
    axgen.1
    alrimiv
end
