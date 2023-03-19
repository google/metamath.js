include "csubrg.mm"
include "cfv.mm"
include "wcel.mm"
include "w3a.mm"
include "cress.mm"
include "co.mm"
include "cmulr.mm"
include "cbs.mm"
include "crg.mm"
include "eqid.mm"
include "subrgring.mm"
include "3ad2ant1.mm"
include "simp2.mm"
include "wceq.mm"
include "subrgbas.mm"
include "eleqtrd.mm"
include "simp3.mm"
include "ringcl.mm"
include "syl3anc.mm"
include "ressmulr.mm"
include "oveqd.mm"
include "3eltr4d.mm"

theorem subrgmcl
  let cA: class A
  let cR: class R
  let c.x: class .x.
  let cX: class X
  let cY: class Y
  assume subrgmcl.p: |- .x. = ( .r ` R )


  assert |- ( ( A e. ( SubRing ` R ) /\ X e. A /\ Y e. A ) -> ( X .x. Y ) e. A )

  proof
    cA
    cR
    csubrg
    cfv
    #
    wcel
    #
    cX
    cA
    wcel
    #
    cY
    cA
    wcel
    #
    w3a
    #
    cX
    cY
    cR
    cA
    cress
    co
    #
    cmulr
    cfv
    #
    co
    #
    @5
    cbs
    cfv
    #
    cX
    cY
    c.x
    co
    cA
    @4
    @5
    crg
    wcel
    #
    cX
    @8
    wcel
    cY
    @8
    wcel
    @7
    @8
    wcel
    @1
    @2
    @9
    @3
    cA
    cR
    @5
    @5
    eqid
    #
    subrgring
    3ad2ant1
    @4
    cX
    cA
    @8
    @1
    @2
    @3
    simp2
    @1
    @2
    cA
    @8
    wceq
    @3
    cA
    cR
    @5
    @10
    subrgbas
    3ad2ant1
    #
    eleqtrd
    @4
    cY
    cA
    @8
    @1
    @2
    @3
    simp3
    @11
    eleqtrd
    @8
    @5
    @6
    cX
    cY
    @8
    eqid
    @6
    eqid
    ringcl
    syl3anc
    @4
    c.x
    @6
    cX
    cY
    @1
    @2
    c.x
    @6
    wceq
    @3
    cA
    cR
    @5
    c.x
    @0
    @10
    subrgmcl.p
    ressmulr
    3ad2ant1
    oveqd
    @11
    3eltr4d
end
