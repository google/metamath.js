include "c0.mm"
include "cfv.mm"
include "0ex.mm"
include "strfvn.mm"
include "0fv.mm"
include "eqtr2i.mm"

theorem str0
  let cF: class F
  let cI: class I
  assume str0.a: |- F = Slot I


  assert |- (/) = ( F ` (/) )

  proof
    c0
    cF
    cfv
    cI
    c0
    cfv
    c0
    c0
    cF
    cI
    0ex
    str0.a
    strfvn
    cI
    0fv
    eqtr2i
end
