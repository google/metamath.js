include "cpreset.mm"
include "wcel.mm"
include "wss.mm"
include "wa.mm"
include "cxp.mm"
include "cin.mm"
include "cdm.mm"
include "cple.mm"
include "cfv.mm"
include "prsss.mm"
include "dmeqd.mm"
include "cress.mm"
include "co.mm"
include "cbs.mm"
include "wceq.mm"
include "ressprs.mm"
include "eqid.mm"
include "prsdm.mm"
include "syl.mm"
include "cvv.mm"
include "ressbas2.mm"
include "fvex.mm"
include "syl6eqel.mm"
include "ressle.mm"
include "adantl.mm"
include "sqxpeqd.mm"
include "ineq12d.mm"
include "3eqtr4d.mm"
include "eqtrd.mm"

theorem prsssdm
  let cA: class A
  let cB: class B
  let cK: class K
  let c.le: class .<_
  let vx: setvar x
  let vy: setvar y
  assume ordtNEW.b: |- B = ( Base ` K )
  assume ordtNEW.l: |- .<_ = ( ( le ` K ) i^i ( B X. B ) )


  assert |- ( ( K e. Preset /\ A C_ B ) -> dom ( .<_ i^i ( A X. A ) ) = A )

  proof
    cK
    cpreset
    wcel
    #
    cA
    cB
    wss
    #
    wa
    #
    c.le
    cA
    cA
    cxp
    #
    cin
    #
    cdm
    cK
    cple
    cfv
    #
    @3
    cin
    #
    cdm
    #
    cA
    @2
    @4
    @6
    cA
    cB
    cK
    c.le
    ordtNEW.b
    ordtNEW.l
    prsss
    dmeqd
    @2
    cK
    cA
    cress
    co
    #
    cple
    cfv
    #
    @8
    cbs
    cfv
    #
    @10
    cxp
    #
    cin
    #
    cdm
    #
    @10
    @7
    cA
    @2
    @8
    cpreset
    wcel
    @13
    @10
    wceq
    cA
    cB
    cK
    ordtNEW.b
    ressprs
    @10
    @8
    @12
    @10
    eqid
    @12
    eqid
    prsdm
    syl
    @2
    @6
    @12
    @2
    @5
    @9
    @3
    @11
    @1
    @5
    @9
    wceq
    #
    @0
    @1
    cA
    cvv
    wcel
    @14
    @1
    cA
    @10
    cvv
    cA
    cB
    @8
    cK
    @8
    eqid
    #
    ordtNEW.b
    ressbas2
    #
    @8
    cbs
    fvex
    syl6eqel
    cA
    cK
    @5
    cvv
    @8
    @15
    @5
    eqid
    ressle
    syl
    adantl
    @2
    cA
    @10
    @1
    cA
    @10
    wceq
    @0
    @16
    adantl
    #
    sqxpeqd
    ineq12d
    dmeqd
    @17
    3eqtr4d
    eqtrd
end
