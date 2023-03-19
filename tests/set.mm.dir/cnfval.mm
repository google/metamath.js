include "ctopon.mm"
include "cfv.mm"
include "wcel.mm"
include "wa.mm"
include "ctop.mm"
include "cv.mm"
include "ccnv.mm"
include "cima.mm"
include "wral.mm"
include "cuni.mm"
include "cmap.mm"
include "co.mm"
include "crab.mm"
include "ccn.mm"
include "cvv.mm"
include "cmpt2.mm"
include "wceq.mm"
include "df-cn.mm"
include "a1i.mm"
include "simprr.mm"
include "unieqd.mm"
include "toponuni.mm"
include "ad2antlr.mm"
include "eqtr4d.mm"
include "simprl.mm"
include "ad2antrr.mm"
include "oveq12d.mm"
include "eleq2d.mm"
include "raleqbidv.mm"
include "rabeqbidv.mm"
include "topontop.mm"
include "adantr.mm"
include "adantl.mm"
include "ovex.mm"
include "rabex.mm"
include "ovmpt2d.mm"

theorem cnfval
  let vy: setvar y
  let vf: setvar f
  let cJ: class J
  let cK: class K
  let cX: class X
  let cY: class Y
  let vj: setvar j
  let vk: setvar k
  let vw: setvar w
  let vx: setvar x
  let vu: setvar u
  let vv: setvar v

  disjoint f y
  disjoint K f
  disjoint K y
  disjoint X f
  disjoint X y
  disjoint Y f
  disjoint Y y
  disjoint J f
  disjoint J y
  disjoint f j
  disjoint f k
  disjoint f w
  disjoint f x
  disjoint j k
  disjoint j w
  disjoint j x
  disjoint j y
  disjoint K j
  disjoint k w
  disjoint k x
  disjoint k y
  disjoint K k
  disjoint w x
  disjoint w y
  disjoint K w
  disjoint x y
  disjoint K x
  disjoint X j
  disjoint X k
  disjoint X w
  disjoint X x
  disjoint Y j
  disjoint Y k
  disjoint Y w
  disjoint Y x
  disjoint f u
  disjoint f v
  disjoint j u
  disjoint j v
  disjoint J j
  disjoint k u
  disjoint k v
  disjoint J k
  disjoint u v
  disjoint u w
  disjoint u x
  disjoint u y
  disjoint J u
  disjoint v w
  disjoint v x
  disjoint v y
  disjoint J v
  disjoint J w
  disjoint J x
  assert |- ( ( J e. ( TopOn ` X ) /\ K e. ( TopOn ` Y ) ) -> ( J Cn K ) = { f e. ( Y ^m X ) | A. y e. K ( `' f " y ) e. J } )

  proof
    cJ
    cX
    ctopon
    cfv
    wcel
    #
    cK
    cY
    ctopon
    cfv
    wcel
    #
    wa
    #
    vj
    vk
    cJ
    cK
    ctop
    ctop
    vf
    cv
    ccnv
    vy
    cv
    cima
    #
    vj
    cv
    #
    wcel
    #
    vy
    vk
    cv
    #
    wral
    #
    vf
    @6
    cuni
    #
    @4
    cuni
    #
    cmap
    co
    #
    crab
    #
    @3
    cJ
    wcel
    #
    vy
    cK
    wral
    #
    vf
    cY
    cX
    cmap
    co
    #
    crab
    #
    ccn
    cvv
    ccn
    vj
    vk
    ctop
    ctop
    @11
    cmpt2
    wceq
    @2
    vy
    vf
    vj
    vk
    df-cn
    a1i
    @2
    @4
    cJ
    wceq
    #
    @6
    cK
    wceq
    #
    wa
    #
    wa
    #
    @7
    @13
    vf
    @10
    @14
    @19
    @8
    cY
    @9
    cX
    cmap
    @19
    @8
    cK
    cuni
    #
    cY
    @19
    @6
    cK
    @2
    @16
    @17
    simprr
    #
    unieqd
    @1
    cY
    @20
    wceq
    @0
    @18
    cY
    cK
    toponuni
    ad2antlr
    eqtr4d
    @19
    @9
    cJ
    cuni
    #
    cX
    @19
    @4
    cJ
    @2
    @16
    @17
    simprl
    #
    unieqd
    @0
    cX
    @22
    wceq
    @1
    @18
    cX
    cJ
    toponuni
    ad2antrr
    eqtr4d
    oveq12d
    @19
    @5
    @12
    vy
    @6
    cK
    @21
    @19
    @4
    cJ
    @3
    @23
    eleq2d
    raleqbidv
    rabeqbidv
    @0
    cJ
    ctop
    wcel
    @1
    cX
    cJ
    topontop
    adantr
    @1
    cK
    ctop
    wcel
    @0
    cY
    cK
    topontop
    adantl
    @15
    cvv
    wcel
    @2
    @13
    vf
    @14
    cY
    cX
    cmap
    ovex
    rabex
    a1i
    ovmpt2d
end
