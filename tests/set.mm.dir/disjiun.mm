include "wdisj.mm"
include "wss.mm"
include "cin.mm"
include "c0.mm"
include "wceq.mm"
include "w3a.mm"
include "wa.mm"
include "cv.mm"
include "ciun.mm"
include "wcel.mm"
include "wn.mm"
include "wal.mm"
include "wrmo.mm"
include "df-disj.mm"
include "wi.mm"
include "wrex.mm"
include "wne.mm"
include "elin.mm"
include "eliun.mm"
include "anbi12i.mm"
include "bitri.mm"
include "weq.mm"
include "wral.mm"
include "wex.mm"
include "nfv.mm"
include "rmo2.mm"
include "an4.mm"
include "ssralv.mm"
include "impcom.mm"
include "r19.29.mm"
include "id.mm"
include "imp.mm"
include "eleq1d.mm"
include "biimpcd.mm"
include "rexlimiv.mm"
include "syl.mm"
include "ex.mm"
include "expimpd.mm"
include "anim12d.mm"
include "inelcm.mm"
include "syl6.mm"
include "exlimiv.mm"
include "syl5bi.mm"
include "expd.mm"
include "sylbi.mm"
include "necon2bd.mm"
include "impancom.mm"
include "3impa.mm"
include "alimdv.mm"
include "eq0.mm"
include "sylibr.mm"

theorem disjiun
  let vx: setvar x
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D
  let vy: setvar y
  let vz: setvar z

  disjoint A x
  disjoint C x
  disjoint D x
  disjoint x y
  disjoint x z
  disjoint y z
  disjoint A y
  disjoint A z
  disjoint B y
  disjoint B z
  disjoint C y
  disjoint C z
  disjoint D y
  disjoint D z
  assert |- ( ( Disj_ x e. A B /\ ( C C_ A /\ D C_ A /\ ( C i^i D ) = (/) ) ) -> ( U_ x e. C B i^i U_ x e. D B ) = (/) )

  proof
    vx
    cA
    cB
    wdisj
    #
    cC
    cA
    wss
    #
    cD
    cA
    wss
    #
    cC
    cD
    cin
    #
    c0
    wceq
    #
    w3a
    #
    wa
    vy
    cv
    #
    vx
    cC
    cB
    ciun
    #
    vx
    cD
    cB
    ciun
    #
    cin
    #
    wcel
    #
    wn
    #
    vy
    wal
    #
    @9
    c0
    wceq
    @5
    @0
    @12
    @0
    @6
    cB
    wcel
    #
    vx
    cA
    wrmo
    #
    vy
    wal
    @5
    @12
    vx
    vy
    cA
    cB
    df-disj
    @5
    @14
    @11
    vy
    @1
    @2
    @4
    @14
    @11
    wi
    @1
    @2
    wa
    #
    @14
    @4
    @11
    @15
    @14
    wa
    #
    @10
    @3
    c0
    @10
    @13
    vx
    cC
    wrex
    #
    @13
    vx
    cD
    wrex
    #
    wa
    #
    @16
    @3
    c0
    wne
    #
    @10
    @6
    @7
    wcel
    #
    @6
    @8
    wcel
    #
    wa
    @19
    @6
    @7
    @8
    elin
    @21
    @17
    @22
    @18
    vx
    @6
    cC
    cB
    eliun
    vx
    @6
    cD
    cB
    eliun
    anbi12i
    bitri
    @14
    @15
    @19
    @20
    wi
    #
    @14
    @13
    vx
    vz
    weq
    #
    wi
    #
    vx
    cA
    wral
    #
    vz
    wex
    #
    @15
    @23
    wi
    @13
    vx
    vz
    cA
    @13
    vz
    nfv
    rmo2
    @27
    @15
    @19
    @20
    @15
    @19
    wa
    @1
    @17
    wa
    #
    @2
    @18
    wa
    #
    wa
    #
    @27
    @20
    @1
    @2
    @17
    @18
    an4
    @26
    @30
    @20
    wi
    vz
    @26
    @30
    vz
    cv
    #
    cC
    wcel
    #
    @31
    cD
    wcel
    #
    wa
    @20
    @26
    @28
    @32
    @29
    @33
    @26
    @1
    @17
    @32
    @26
    @1
    wa
    @25
    vx
    cC
    wral
    #
    @17
    @32
    wi
    @1
    @26
    @34
    @25
    vx
    cC
    cA
    ssralv
    impcom
    @34
    @17
    @32
    @34
    @17
    wa
    @25
    @13
    wa
    #
    vx
    cC
    wrex
    @32
    @25
    @13
    vx
    cC
    r19.29
    @35
    @32
    vx
    cC
    @35
    vx
    cv
    #
    cC
    wcel
    @32
    @35
    @36
    @31
    cC
    @25
    @13
    @24
    @25
    id
    imp
    #
    eleq1d
    biimpcd
    rexlimiv
    syl
    ex
    syl
    expimpd
    @26
    @2
    @18
    @33
    @26
    @2
    wa
    @25
    vx
    cD
    wral
    #
    @18
    @33
    wi
    @2
    @26
    @38
    @25
    vx
    cD
    cA
    ssralv
    impcom
    @38
    @18
    @33
    @38
    @18
    wa
    @35
    vx
    cD
    wrex
    @33
    @25
    @13
    vx
    cD
    r19.29
    @35
    @33
    vx
    cD
    @35
    @36
    cD
    wcel
    @33
    @35
    @36
    @31
    cD
    @37
    eleq1d
    biimpcd
    rexlimiv
    syl
    ex
    syl
    expimpd
    anim12d
    @31
    cC
    cD
    inelcm
    syl6
    exlimiv
    syl5bi
    expd
    sylbi
    impcom
    syl5bi
    necon2bd
    impancom
    3impa
    alimdv
    syl5bi
    impcom
    vy
    @9
    eq0
    sylibr
end
