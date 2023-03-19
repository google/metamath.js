include "cid.mm"
include "wfr.mm"
include "c0.mm"
include "wceq.mm"
include "cv.mm"
include "wcel.mm"
include "wbr.mm"
include "equid.mm"
include "vex.mm"
include "ideq.mm"
include "mpbir.mm"
include "wn.mm"
include "frirr.mm"
include "ex.mm"
include "mt2i.mm"
include "eq0rdv.mm"
include "fr0.mm"
include "freq2.mm"
include "mpbiri.mm"
include "impbii.mm"

theorem ifr0
  let cA: class A
  let vx: setvar x


  assert |- ( _I Fr A <-> A = (/) )

  proof
    cA
    cid
    wfr
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
    @2
    @2
    wceq
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
    frirr
    ex
    mt2i
    eq0rdv
    @1
    @0
    c0
    cid
    wfr
    cid
    fr0
    cA
    c0
    cid
    freq2
    mpbiri
    impbii
end
