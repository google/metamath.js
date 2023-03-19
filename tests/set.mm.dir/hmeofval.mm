include "ctop.mm"
include "wcel.mm"
include "wa.mm"
include "chmeo.mm"
include "co.mm"
include "cv.mm"
include "ccnv.mm"
include "ccn.mm"
include "crab.mm"
include "wceq.mm"
include "oveq12.mm"
include "ancoms.mm"
include "eleq2d.mm"
include "rabeqbidv.mm"
include "df-hmeo.mm"
include "ovex.mm"
include "rabex.mm"
include "ovmpt2a.mm"
include "wn.mm"
include "c0.mm"
include "mpt2ndm0.mm"
include "wral.mm"
include "cntop1.mm"
include "cntop2.mm"
include "jca.mm"
include "a1d.mm"
include "con3rr3.mm"
include "ralrimiv.mm"
include "rabeq0.mm"
include "sylibr.mm"
include "eqtr4d.mm"
include "pm2.61i.mm"

theorem hmeofval
  let vf: setvar f
  let cJ: class J
  let cK: class K
  let vj: setvar j
  let vk: setvar k

  disjoint J f
  disjoint K f
  disjoint f j
  disjoint f k
  disjoint j k
  disjoint J j
  disjoint J k
  disjoint K j
  disjoint K k
  assert |- ( J Homeo K ) = { f e. ( J Cn K ) | `' f e. ( K Cn J ) }

  proof
    cJ
    ctop
    wcel
    #
    cK
    ctop
    wcel
    #
    wa
    #
    cJ
    cK
    chmeo
    co
    #
    vf
    cv
    #
    ccnv
    #
    cK
    cJ
    ccn
    co
    #
    wcel
    #
    vf
    cJ
    cK
    ccn
    co
    #
    crab
    #
    wceq
    vj
    vk
    cJ
    cK
    ctop
    ctop
    @5
    vk
    cv
    #
    vj
    cv
    #
    ccn
    co
    #
    wcel
    #
    vf
    @11
    @10
    ccn
    co
    #
    crab
    #
    @9
    chmeo
    @11
    cJ
    wceq
    #
    @10
    cK
    wceq
    #
    wa
    #
    @13
    @7
    vf
    @14
    @8
    @11
    cJ
    @10
    cK
    ccn
    oveq12
    @18
    @12
    @6
    @5
    @17
    @16
    @12
    @6
    wceq
    @10
    cK
    @11
    cJ
    ccn
    oveq12
    ancoms
    eleq2d
    rabeqbidv
    vf
    vj
    vk
    df-hmeo
    #
    @7
    vf
    @8
    cJ
    cK
    ccn
    ovex
    rabex
    ovmpt2a
    @2
    wn
    #
    @3
    c0
    @9
    vj
    vk
    @15
    chmeo
    cJ
    cK
    ctop
    ctop
    @19
    mpt2ndm0
    @20
    @7
    wn
    #
    vf
    @8
    wral
    @9
    c0
    wceq
    @20
    @21
    vf
    @8
    @4
    @8
    wcel
    #
    @7
    @2
    @22
    @2
    @7
    @22
    @0
    @1
    @4
    cJ
    cK
    cntop1
    @4
    cJ
    cK
    cntop2
    jca
    a1d
    con3rr3
    ralrimiv
    @7
    vf
    @8
    rabeq0
    sylibr
    eqtr4d
    pm2.61i
end
