include "casa.mm"
include "wcel.mm"
include "wa.mm"
include "w3a.mm"
include "co.mm"
include "wceq.mm"
include "simp1.mm"
include "simpr.mm"
include "3ad2ant2.mm"
include "clmod.mm"
include "assalmod.mm"
include "simpl.mm"
include "lmodvscl.mm"
include "syl3an.mm"
include "3ad2ant3.mm"
include "assaassr.mm"
include "syl13anc.mm"
include "assaass.mm"
include "eqcomd.mm"
include "3ad2ant1.mm"
include "lmodvsass.mm"
include "oveq1d.mm"
include "crg.mm"
include "ccrg.mm"
include "assasca.mm"
include "crngring.mm"
include "syl.mm"
include "adantr.mm"
include "adantl.mm"
include "ringcl.mm"
include "syl3anc.mm"
include "3adant3.mm"
include "eqtrd.mm"
include "3eqtrd.mm"

theorem assa2ass
  let cA: class A
  let cB: class B
  let cC: class C
  let c.x: class .x.
  let c.xp: class .X.
  let cF: class F
  let c.as: class .*
  let cV: class V
  let cW: class W
  let cX: class X
  let cY: class Y
  assume assa2ass.v: |- V = ( Base ` W )
  assume assa2ass.f: |- F = ( Scalar ` W )
  assume assa2ass.b: |- B = ( Base ` F )
  assume assa2ass.m: |- .* = ( .r ` F )
  assume assa2ass.s: |- .x. = ( .s ` W )
  assume assa2ass.t: |- .X. = ( .r ` W )


  assert |- ( ( W e. AssAlg /\ ( A e. B /\ C e. B ) /\ ( X e. V /\ Y e. V ) ) -> ( ( A .x. X ) .X. ( C .x. Y ) ) = ( ( C .* A ) .x. ( X .X. Y ) ) )

  proof
    cW
    casa
    wcel
    #
    cA
    cB
    wcel
    #
    cC
    cB
    wcel
    #
    wa
    #
    cX
    cV
    wcel
    #
    cY
    cV
    wcel
    #
    wa
    #
    w3a
    #
    cA
    cX
    c.x
    co
    #
    cC
    cY
    c.x
    co
    c.xp
    co
    #
    cC
    @8
    cY
    c.xp
    co
    c.x
    co
    #
    cC
    @8
    c.x
    co
    #
    cY
    c.xp
    co
    #
    cC
    cA
    c.as
    co
    #
    cX
    cY
    c.xp
    co
    c.x
    co
    #
    @7
    @0
    @2
    @8
    cV
    wcel
    #
    @5
    @9
    @10
    wceq
    @0
    @3
    @6
    simp1
    #
    @3
    @0
    @2
    @6
    @1
    @2
    simpr
    #
    3ad2ant2
    #
    @0
    cW
    clmod
    wcel
    #
    @3
    @1
    @6
    @4
    @15
    cW
    assalmod
    #
    @1
    @2
    simpl
    #
    @4
    @5
    simpl
    #
    cA
    c.x
    cF
    cB
    cV
    cW
    cX
    assa2ass.v
    assa2ass.f
    assa2ass.s
    assa2ass.b
    lmodvscl
    syl3an
    #
    @6
    @0
    @5
    @3
    @4
    @5
    simpr
    3ad2ant3
    #
    cC
    cB
    c.x
    c.xp
    cF
    cV
    cW
    @8
    cY
    assa2ass.v
    assa2ass.f
    assa2ass.b
    assa2ass.s
    assa2ass.t
    assaassr
    syl13anc
    @7
    @0
    @2
    @15
    @5
    @10
    @12
    wceq
    @16
    @18
    @23
    @24
    @0
    @2
    @15
    @5
    w3a
    wa
    @12
    @10
    cC
    cB
    c.x
    c.xp
    cF
    cV
    cW
    @8
    cY
    assa2ass.v
    assa2ass.f
    assa2ass.b
    assa2ass.s
    assa2ass.t
    assaass
    eqcomd
    syl13anc
    @7
    @12
    @13
    cX
    c.x
    co
    #
    cY
    c.xp
    co
    #
    @14
    @7
    @19
    @2
    @1
    @4
    @12
    @26
    wceq
    @0
    @3
    @19
    @6
    @20
    3ad2ant1
    @18
    @3
    @0
    @1
    @6
    @21
    3ad2ant2
    @6
    @0
    @4
    @3
    @22
    3ad2ant3
    #
    @19
    @2
    @1
    @4
    w3a
    wa
    #
    @11
    @25
    cY
    c.xp
    @28
    @25
    @11
    cC
    cA
    c.x
    c.as
    cF
    cB
    cV
    cW
    cX
    assa2ass.v
    assa2ass.f
    assa2ass.s
    assa2ass.b
    assa2ass.m
    lmodvsass
    eqcomd
    oveq1d
    syl13anc
    @7
    @0
    @13
    cB
    wcel
    #
    @4
    @5
    @26
    @14
    wceq
    @16
    @0
    @3
    @29
    @6
    @0
    @3
    wa
    cF
    crg
    wcel
    #
    @2
    @1
    @29
    @0
    @30
    @3
    @0
    cF
    ccrg
    wcel
    @30
    cF
    cW
    assa2ass.f
    assasca
    cF
    crngring
    syl
    adantr
    @3
    @2
    @0
    @17
    adantl
    @3
    @1
    @0
    @21
    adantl
    cB
    cF
    c.as
    cC
    cA
    assa2ass.b
    assa2ass.m
    ringcl
    syl3anc
    3adant3
    @27
    @24
    @13
    cB
    c.x
    c.xp
    cF
    cV
    cW
    cX
    cY
    assa2ass.v
    assa2ass.f
    assa2ass.b
    assa2ass.s
    assa2ass.t
    assaass
    syl13anc
    eqtrd
    3eqtrd
end
