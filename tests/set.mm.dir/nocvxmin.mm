include "c0.mm"
include "wne.mm"
include "csur.mm"
include "wss.mm"
include "cv.mm"
include "cslt.mm"
include "wbr.mm"
include "wa.mm"
include "wcel.mm"
include "wi.mm"
include "wral.mm"
include "w3a.mm"
include "cbday.mm"
include "cfv.mm"
include "cima.mm"
include "cint.mm"
include "wceq.mm"
include "wrex.mm"
include "weq.mm"
include "wreu.mm"
include "con0.mm"
include "crn.mm"
include "imassrn.mm"
include "bdayrn.mm"
include "sseqtri.mm"
include "wex.mm"
include "cdm.mm"
include "bdaydm.mm"
include "sseq2i.mm"
include "wfun.mm"
include "bdayfun.mm"
include "funfvima2.mm"
include "mpan.mm"
include "sylbir.mm"
include "elex2.mm"
include "syl6.mm"
include "exlimdv.mm"
include "n0.mm"
include "3imtr4g.mm"
include "impcom.mm"
include "onint.mm"
include "sylancr.mm"
include "wb.mm"
include "wfn.mm"
include "bdayfn.mm"
include "fvelimab.mm"
include "adantl.mm"
include "mpbid.mm"
include "3adant3.mm"
include "wn.mm"
include "ssel.mm"
include "anim12d.mm"
include "imp.mm"
include "ad2ant2r.mm"
include "nocvxminlem.mm"
include "ancom.mm"
include "anbi12i.mm"
include "syl5bi.mm"
include "slttrieq2.mm"
include "biimpar.mm"
include "syl12anc.mm"
include "exp32.mm"
include "ralrimivv.mm"
include "3adant1.mm"
include "fveq2.mm"
include "eqeq1d.mm"
include "reu4.mm"
include "sylanbrc.mm"

theorem nocvxmin
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let vw: setvar w
  let cA: class A
  let vt: setvar t

  disjoint A w
  disjoint A x
  disjoint A y
  disjoint A z
  disjoint w x
  disjoint w y
  disjoint w z
  disjoint x y
  disjoint x z
  disjoint y z
  disjoint A t
  disjoint t w
  disjoint t x
  disjoint t y
  disjoint t z
  assert |- ( ( A =/= (/) /\ A C_ No /\ A. x e. A A. y e. A A. z e. No ( ( x <s z /\ z <s y ) -> z e. A ) ) -> E! w e. A ( bday ` w ) = |^| ( bday " A ) )

  proof
    cA
    c0
    wne
    #
    cA
    csur
    wss
    #
    vx
    cv
    #
    vz
    cv
    #
    cslt
    wbr
    @3
    vy
    cv
    cslt
    wbr
    wa
    @3
    cA
    wcel
    wi
    vz
    csur
    wral
    vy
    cA
    wral
    vx
    cA
    wral
    #
    w3a
    vw
    cv
    #
    cbday
    cfv
    #
    cbday
    cA
    cima
    #
    cint
    #
    wceq
    #
    vw
    cA
    wrex
    #
    @9
    vt
    cv
    #
    cbday
    cfv
    #
    @8
    wceq
    #
    wa
    #
    vw
    vt
    weq
    #
    wi
    #
    vt
    cA
    wral
    vw
    cA
    wral
    #
    @9
    vw
    cA
    wreu
    @0
    @1
    @10
    @4
    @0
    @1
    wa
    #
    @8
    @7
    wcel
    #
    @10
    @18
    @7
    con0
    wss
    @7
    c0
    wne
    #
    @19
    @7
    cbday
    crn
    con0
    cbday
    cA
    imassrn
    bdayrn
    sseqtri
    @1
    @0
    @20
    @1
    @2
    cA
    wcel
    #
    vx
    wex
    @5
    @7
    wcel
    vw
    wex
    #
    @0
    @20
    @1
    @21
    @22
    vx
    @1
    @21
    @2
    cbday
    cfv
    #
    @7
    wcel
    #
    @22
    @1
    cA
    cbday
    cdm
    #
    wss
    #
    @21
    @24
    wi
    #
    @25
    csur
    cA
    bdaydm
    sseq2i
    cbday
    wfun
    @26
    @27
    bdayfun
    cA
    @2
    cbday
    funfvima2
    mpan
    sylbir
    vw
    @23
    @7
    elex2
    syl6
    exlimdv
    vx
    cA
    n0
    vw
    @7
    n0
    3imtr4g
    impcom
    @7
    onint
    sylancr
    @1
    @19
    @10
    wb
    #
    @0
    cbday
    csur
    wfn
    @1
    @28
    bdayfn
    vw
    csur
    cA
    @8
    cbday
    fvelimab
    mpan
    adantl
    mpbid
    3adant3
    @1
    @4
    @17
    @0
    @1
    @4
    wa
    #
    @16
    vw
    vt
    cA
    cA
    @29
    @5
    cA
    wcel
    #
    @11
    cA
    wcel
    #
    wa
    #
    @14
    @15
    @29
    @32
    @14
    wa
    #
    wa
    @5
    csur
    wcel
    #
    @11
    csur
    wcel
    #
    wa
    #
    @5
    @11
    cslt
    wbr
    wn
    #
    @11
    @5
    cslt
    wbr
    wn
    #
    @15
    @1
    @32
    @36
    @4
    @14
    @1
    @32
    @36
    @1
    @30
    @34
    @31
    @35
    cA
    csur
    @5
    ssel
    cA
    csur
    @11
    ssel
    anim12d
    imp
    ad2ant2r
    @29
    @33
    @37
    vx
    vy
    vz
    cA
    @5
    @11
    nocvxminlem
    imp
    @29
    @33
    @38
    @33
    @31
    @30
    wa
    #
    @13
    @9
    wa
    #
    wa
    @29
    @38
    @32
    @39
    @14
    @40
    @30
    @31
    ancom
    @9
    @13
    ancom
    anbi12i
    vx
    vy
    vz
    cA
    @11
    @5
    nocvxminlem
    syl5bi
    imp
    @36
    @15
    @37
    @38
    wa
    @5
    @11
    slttrieq2
    biimpar
    syl12anc
    exp32
    ralrimivv
    3adant1
    @9
    @13
    vw
    vt
    cA
    @15
    @6
    @12
    @8
    @5
    @11
    cbday
    fveq2
    eqeq1d
    reu4
    sylanbrc
end
