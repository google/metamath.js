include "wbr.mm"
include "cvv.mm"
include "cep.mm"
include "ctxp.mm"
include "csymdif.mm"
include "crn.mm"
include "wn.mm"
include "cv.mm"
include "wcel.mm"
include "wb.mm"
include "wal.mm"
include "cdif.mm"
include "wa.mm"
include "breqi.mm"
include "brdif.mm"
include "bitri.mm"
include "mpbiran.mm"
include "brtxpsd.mm"

theorem brtxpsd2
  let vx: setvar x
  let cA: class A
  let cB: class B
  let cC: class C
  let cR: class R
  let cS: class S
  assume brtxpsd2.1: |- A e. _V
  assume brtxpsd2.2: |- B e. _V
  assume brtxpsd2.3: |- R = ( C \ ran ( ( _V (x) _E ) /_\ ( S (x) _V ) ) )
  assume brtxpsd2.4: |- A C B

  disjoint A x
  disjoint B x
  disjoint S x
  assert |- ( A R B <-> A. x ( x e. B <-> x S A ) )

  proof
    cA
    cB
    cR
    wbr
    #
    cA
    cB
    cvv
    cep
    ctxp
    cS
    cvv
    ctxp
    csymdif
    crn
    #
    wbr
    wn
    #
    vx
    cv
    #
    cB
    wcel
    @3
    cA
    cS
    wbr
    wb
    vx
    wal
    @0
    cA
    cB
    cC
    wbr
    #
    @2
    brtxpsd2.4
    @0
    cA
    cB
    cC
    @1
    cdif
    #
    wbr
    @4
    @2
    wa
    cA
    cB
    cR
    @5
    brtxpsd2.3
    breqi
    cA
    cB
    cC
    @1
    brdif
    bitri
    mpbiran
    vx
    cA
    cB
    cS
    brtxpsd2.1
    brtxpsd2.2
    brtxpsd
    bitri
end
