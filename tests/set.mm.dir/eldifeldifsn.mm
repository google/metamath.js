include "wcel.mm"
include "cdif.mm"
include "csn.mm"
include "snssi.mm"
include "sscond.mm"
include "sselda.mm"

theorem eldifeldifsn
  let cA: class A
  let cB: class B
  let cX: class X
  let cY: class Y


  assert |- ( ( X e. A /\ Y e. ( B \ A ) ) -> Y e. ( B \ { X } ) )

  proof
    cX
    cA
    wcel
    #
    cB
    cA
    cdif
    cB
    cX
    csn
    #
    cdif
    cY
    @0
    @1
    cA
    cB
    cX
    cA
    snssi
    sscond
    sselda
end
