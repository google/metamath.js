include "cfv.mm"
include "wceq.mm"
include "wtru.mm"
include "cvv.mm"
include "wcel.mm"
include "a1i.mm"
include "strfvnd.mm"
include "trud.mm"

theorem strfvn
  let cS: class S
  let cE: class E
  let cN: class N
  assume strfvn.f: |- S e. _V
  assume strfvn.c: |- E = Slot N


  assert |- ( E ` S ) = ( S ` N )

  proof
    cS
    cE
    cfv
    cN
    cS
    cfv
    wceq
    wtru
    cS
    cE
    cN
    cvv
    strfvn.c
    cS
    cvv
    wcel
    wtru
    strfvn.f
    a1i
    strfvnd
    trud
end
