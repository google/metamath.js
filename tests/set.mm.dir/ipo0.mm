include "cid.mm"
include "wpo.mm"
include "c0.mm"
include "wceq.mm"
include "cv.mm"
include "wcel.mm"
include "wbr.mm"
include "weq.mm"
include "equid.mm"
include "vex.mm"
include "ideq.mm"
include "mpbir.mm"
include "wn.mm"
include "poirr.mm"
include "ex.mm"
include "mt2i.mm"
include "eq0rdv.mm"
include "po0.mm"
include "poeq2.mm"
include "mpbiri.mm"
include "impbii.mm"

theorem ipo0
  let cA: class A
  let vx: setvar x


  assert |- ( _I Po A <-> A = (/) )

  proof
    cA
    cid
    wpo
    #
    cA
    c0
    wceq
    #
    @0
    vx
    cA
    @0
    vx
    cv
    #
    cA
    wcel
    #
    @2
    @2
    cid
    wbr
    #
    @4
    vx
    vx
    weq
    vx
    equid
    @2
    @2
    vx
    vex
    ideq
    mpbir
    @0
    @3
    @4
    wn
    cA
    @2
    cid
    poirr
    ex
    mt2i
    eq0rdv
    @1
    @0
    c0
    cid
    wpo
    cid
    po0
    cA
    c0
    cid
    poeq2
    mpbiri
    impbii
end
