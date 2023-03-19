include "c0.mm"
include "wne.mm"
include "con0.mm"
include "wcel.mm"
include "cv.mm"
include "csdm.mm"
include "wbr.mm"
include "wrex.mm"
include "wral.mm"
include "w3a.mm"
include "com.mm"
include "wss.mm"
include "wn.mm"
include "wceq.mm"
include "csuc.mm"
include "wo.mm"
include "nn0suc.mm"
include "simp1.mm"
include "necon2bi.mm"
include "wa.mm"
include "wi.mm"
include "vex.mm"
include "sucid.mm"
include "eleq2.mm"
include "mpbiri.mm"
include "adantl.mm"
include "breq1.mm"
include "rexbidv.mm"
include "breq2.mm"
include "cbvrexv.mm"
include "syl6bb.mm"
include "rspcv.mm"
include "syl.mm"
include "cdom.mm"
include "cvv.mm"
include "biimpa.mm"
include "3ad2antl2.mm"
include "wb.mm"
include "nnon.mm"
include "suceloni.mm"
include "eleq1.mm"
include "biimparc.mm"
include "sylan.mm"
include "3adant3.mm"
include "onelon.mm"
include "simpl1.mm"
include "onsssuc.mm"
include "syl2anc.mm"
include "mpbird.mm"
include "ssdomg.mm"
include "mpsyl.mm"
include "domnsym.mm"
include "nrexdv.mm"
include "3expia.mm"
include "pm2.65d.mm"
include "intn3an3d.mm"
include "rexlimiva.mm"
include "jaoi.mm"
include "con2i.mm"
include "word.mm"
include "ordom.mm"
include "eloni.mm"
include "3ad2ant2.mm"
include "ordtri1.mm"
include "sylancr.mm"

theorem winainflem
  let vx: setvar x
  let vy: setvar y
  let cA: class A
  let vw: setvar w
  let vz: setvar z

  disjoint A x
  disjoint A y
  disjoint x y
  disjoint A w
  disjoint A z
  disjoint w x
  disjoint w y
  disjoint w z
  disjoint x z
  disjoint y z
  assert |- ( ( A =/= (/) /\ A e. On /\ A. x e. A E. y e. A x ~< y ) -> _om C_ A )

  proof
    cA
    c0
    wne
    #
    cA
    con0
    wcel
    #
    vx
    cv
    #
    vy
    cv
    #
    csdm
    wbr
    #
    vy
    cA
    wrex
    #
    vx
    cA
    wral
    #
    w3a
    #
    com
    cA
    wss
    #
    cA
    com
    wcel
    #
    wn
    #
    @9
    @7
    @9
    cA
    c0
    wceq
    #
    cA
    vz
    cv
    #
    csuc
    #
    wceq
    #
    vz
    com
    wrex
    #
    wo
    @7
    wn
    #
    vz
    cA
    nn0suc
    @11
    @16
    @15
    @7
    cA
    c0
    @0
    @1
    @6
    simp1
    necon2bi
    @14
    @16
    vz
    com
    @12
    com
    wcel
    #
    @14
    wa
    #
    @6
    @0
    @1
    @18
    @6
    @12
    vw
    cv
    #
    csdm
    wbr
    #
    vw
    cA
    wrex
    #
    @18
    @12
    cA
    wcel
    #
    @6
    @21
    wi
    @14
    @22
    @17
    @14
    @22
    @12
    @13
    wcel
    @12
    vz
    vex
    #
    sucid
    cA
    @13
    @12
    eleq2
    mpbiri
    adantl
    @5
    @21
    vx
    @12
    cA
    @2
    @12
    wceq
    #
    @5
    @12
    @3
    csdm
    wbr
    #
    vy
    cA
    wrex
    @21
    @24
    @4
    @25
    vy
    cA
    @2
    @12
    @3
    csdm
    breq1
    rexbidv
    @25
    @20
    vy
    vw
    cA
    @3
    @19
    @12
    csdm
    breq2
    cbvrexv
    syl6bb
    rspcv
    syl
    @17
    @14
    @6
    @21
    wn
    @17
    @14
    @6
    w3a
    #
    @20
    vw
    cA
    @26
    @19
    cA
    wcel
    #
    wa
    #
    @19
    @12
    cdom
    wbr
    #
    @20
    wn
    @12
    cvv
    wcel
    @28
    @19
    @12
    wss
    #
    @29
    @23
    @28
    @30
    @19
    @13
    wcel
    #
    @14
    @17
    @27
    @31
    @6
    @14
    @27
    @31
    cA
    @13
    @19
    eleq2
    biimpa
    3ad2antl2
    @28
    @19
    con0
    wcel
    #
    @12
    con0
    wcel
    #
    @30
    @31
    wb
    @26
    @1
    @27
    @32
    @17
    @14
    @1
    @6
    @17
    @13
    con0
    wcel
    #
    @14
    @1
    @17
    @33
    @34
    @12
    nnon
    #
    @12
    suceloni
    syl
    @14
    @1
    @34
    cA
    @13
    con0
    eleq1
    biimparc
    sylan
    3adant3
    cA
    @19
    onelon
    sylan
    @28
    @17
    @33
    @17
    @14
    @6
    @27
    simpl1
    @35
    syl
    @19
    @12
    onsssuc
    syl2anc
    mpbird
    @19
    @12
    cvv
    ssdomg
    mpsyl
    @19
    @12
    domnsym
    syl
    nrexdv
    3expia
    pm2.65d
    intn3an3d
    rexlimiva
    jaoi
    syl
    con2i
    @7
    com
    word
    cA
    word
    #
    @8
    @10
    wb
    ordom
    @1
    @0
    @36
    @6
    cA
    eloni
    3ad2ant2
    com
    cA
    ordtri1
    sylancr
    mpbird
end
