include "cr.mm"
include "wcel.mm"
include "wa.mm"
include "cle.mm"
include "wbr.mm"
include "cioo.mm"
include "co.mm"
include "cvol.mm"
include "cfv.mm"
include "cmin.mm"
include "cc0.mm"
include "cif.mm"
include "wceq.mm"
include "volioo.mm"
include "3expa.mm"
include "iftrue.mm"
include "adantl.mm"
include "eqtr4d.mm"
include "wn.mm"
include "clt.mm"
include "simpl.mm"
include "simpr.mm"
include "wb.mm"
include "ltnled.mm"
include "adantr.mm"
include "mpbird.mm"
include "c0.mm"
include "vol0.mm"
include "a1i.mm"
include "ltled.mm"
include "cxr.mm"
include "rexrd.mm"
include "ioo0.mm"
include "syl2anc.mm"
include "fveq2d.mm"
include "biimpa.mm"
include "iffalsed.mm"
include "3eqtr4d.mm"
include "pm2.61dan.mm"

theorem volioore
  let cA: class A
  let cB: class B
  let vk: setvar k
  let vx: setvar x


  assert |- ( ( A e. RR /\ B e. RR ) -> ( vol ` ( A (,) B ) ) = if ( A <_ B , ( B - A ) , 0 ) )

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
    cioo
    co
    #
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
    @5
    @6
    @7
    @0
    @1
    @3
    @5
    @6
    wceq
    cA
    cB
    volioo
    3expa
    @3
    @7
    @6
    wceq
    @2
    @3
    @6
    cc0
    iftrue
    adantl
    eqtr4d
    @2
    @3
    wn
    #
    wa
    #
    @2
    cB
    cA
    clt
    wbr
    #
    @8
    @2
    @9
    simpl
    @10
    @11
    @9
    @2
    @9
    simpr
    @2
    @11
    @9
    wb
    @9
    @2
    cB
    cA
    @0
    @1
    simpr
    #
    @0
    @1
    simpl
    #
    ltnled
    #
    adantr
    mpbird
    @2
    @11
    wa
    #
    c0
    cvol
    cfv
    #
    cc0
    @5
    @7
    @16
    cc0
    wceq
    @15
    vol0
    a1i
    @15
    @4
    c0
    cvol
    @15
    @4
    c0
    wceq
    #
    cB
    cA
    cle
    wbr
    #
    @15
    cB
    cA
    @2
    @1
    @11
    @12
    adantr
    @2
    @0
    @11
    @13
    adantr
    @2
    @11
    simpr
    ltled
    @2
    @17
    @18
    wb
    #
    @11
    @2
    cA
    cxr
    wcel
    cB
    cxr
    wcel
    @19
    @2
    cA
    @13
    rexrd
    @2
    cB
    @12
    rexrd
    cA
    cB
    ioo0
    syl2anc
    adantr
    mpbird
    fveq2d
    @15
    @3
    @6
    cc0
    @2
    @11
    @9
    @14
    biimpa
    iffalsed
    3eqtr4d
    syl2anc
    pm2.61dan
end
