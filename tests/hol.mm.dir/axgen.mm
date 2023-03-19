include "kt.mm"
include "alrimiv.mm"

theorem axgen
  param hal: type al
  param vx: var x
  param tr: term R
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
