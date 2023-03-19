include "wcel.mm"
include "cxp.mm"
include "csn.mm"
include "cima.mm"
include "c0.mm"
include "cif.mm"
include "bj-xpimasn.mm"
include "iftrue.mm"
include "syl5eq.mm"

theorem bj-xpima2sn
  let cA: class A
  let cB: class B
  let cX: class X


  assert |- ( X e. A -> ( ( A X. B ) " { X } ) = B )

  proof
    cX
    cA
    wcel
    #
    cA
    cB
    cxp
    cX
    csn
    cima
    @0
    cB
    c0
    cif
    cB
    cA
    cB
    cX
    bj-xpimasn
    @0
    cB
    c0
    iftrue
    syl5eq
end
