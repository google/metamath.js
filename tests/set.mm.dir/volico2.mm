include "cr.mm"
include "wcel.mm"
include "wa.mm"
include "cle.mm"
include "wbr.mm"
include "cico.mm"
include "co.mm"
include "cvol.mm"
include "cfv.mm"
include "cmin.mm"
include "cc0.mm"
include "cif.mm"
include "wceq.mm"
include "clt.mm"
include "iftrue.mm"
include "adantl.mm"
include "volico.mm"
include "adantr.mm"
include "simpll.mm"
include "simplr.mm"
include "simpr.mm"
include "ltled.mm"
include "iftrued.mm"
include "3eqtr4d.mm"
include "adantlr.mm"
include "wn.mm"
include "simpld.mm"
include "simprd.mm"
include "lenlteq.mm"
include "eqcomd.mm"
include "eqled.mm"
include "lenltd.mm"
include "mpbid.mm"
include "iffalsed.mm"
include "recn.mm"
include "subidd.mm"
include "ad2antrr.mm"
include "oveq1.mm"
include "3eqtrd.mm"
include "syl2anc.mm"
include "pm2.61dan.mm"
include "stoic1a.mm"
include "iffalse.mm"

theorem volico2
  let cA: class A
  let cB: class B
  let vk: setvar k
  let vx: setvar x


  assert |- ( ( A e. RR /\ B e. RR ) -> ( vol ` ( A [,) B ) ) = if ( A <_ B , ( B - A ) , 0 ) )

  proof
    cA
    cr
    wcel
    #
    cB
    cr
    wcel
    #
    wa
    #
    cA
    cB
    cle
    wbr
    #
    cA
    cB
    cico
    co
    cvol
    cfv
    #
    @3
    cB
    cA
    cmin
    co
    #
    cc0
    cif
    #
    wceq
    #
    @2
    @3
    wa
    #
    cA
    cB
    clt
    wbr
    #
    @7
    @2
    @9
    @7
    @3
    @2
    @9
    wa
    #
    @9
    @5
    cc0
    cif
    #
    @5
    @4
    @6
    @9
    @11
    @5
    wceq
    @2
    @9
    @5
    cc0
    iftrue
    adantl
    @2
    @4
    @11
    wceq
    #
    @9
    cA
    cB
    volico
    #
    adantr
    @10
    @3
    @5
    cc0
    @10
    cA
    cB
    @0
    @1
    @9
    simpll
    @0
    @1
    @9
    simplr
    @2
    @9
    simpr
    ltled
    #
    iftrued
    3eqtr4d
    adantlr
    @8
    @9
    wn
    #
    wa
    #
    @2
    cA
    cB
    wceq
    #
    @7
    @2
    @3
    @15
    simpll
    #
    @16
    cA
    cB
    @16
    @0
    @1
    @18
    simpld
    @16
    @0
    @1
    @18
    simprd
    @2
    @3
    @15
    simplr
    @8
    @15
    simpr
    lenlteq
    @2
    @17
    wa
    #
    @11
    @5
    @4
    @6
    @19
    @11
    cc0
    cA
    cA
    cmin
    co
    #
    @5
    @19
    @9
    @5
    cc0
    @19
    cB
    cA
    cle
    wbr
    @15
    @19
    cB
    cA
    @0
    @1
    @17
    simplr
    #
    @19
    cA
    cB
    @2
    @17
    simpr
    #
    eqcomd
    eqled
    @19
    cB
    cA
    @21
    @0
    @1
    @17
    simpll
    #
    lenltd
    mpbid
    iffalsed
    @0
    cc0
    @20
    wceq
    @1
    @17
    @0
    @20
    cc0
    @0
    cA
    cA
    recn
    subidd
    eqcomd
    ad2antrr
    @17
    @20
    @5
    wceq
    @2
    cA
    cB
    cA
    cmin
    oveq1
    adantl
    3eqtrd
    @2
    @12
    @17
    @13
    adantr
    @19
    @3
    @5
    cc0
    @19
    cA
    cB
    @23
    @22
    eqled
    iftrued
    3eqtr4d
    syl2anc
    pm2.61dan
    @2
    @3
    wn
    #
    wa
    #
    @11
    cc0
    @4
    @6
    @25
    @9
    @5
    cc0
    @2
    @9
    @3
    @14
    stoic1a
    iffalsed
    @2
    @12
    @24
    @13
    adantr
    @24
    @6
    cc0
    wceq
    @2
    @3
    @5
    cc0
    iffalse
    adantl
    3eqtr4d
    pm2.61dan
end
