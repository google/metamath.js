include "cen.mm"
include "wbr.mm"
include "cv.mm"
include "wf1o.mm"
include "wex.mm"
include "cab.mm"
include "bren.mm"
include "wa.mm"
include "eeanv.mm"
include "ccom.mm"
include "ccnv.mm"
include "cmap.mm"
include "co.mm"
include "wss.mm"
include "cvv.mm"
include "wcel.mm"
include "wf.mm"
include "f1of.mm"
include "wb.mm"
include "cdm.mm"
include "f1odm.mm"
include "vex.mm"
include "dmex.mm"
include "syl6eqelr.mm"
include "elmapg.mm"
include "syl2anr.mm"
include "syl5ibr.mm"
include "abssdv.mm"
include "ovex.mm"
include "ssex.mm"
include "syl.mm"
include "crn.mm"
include "wfo.mm"
include "wceq.mm"
include "f1ofo.mm"
include "forn.mm"
include "rnex.mm"
include "f1oco.mm"
include "adantll.mm"
include "f1ocnv.mm"
include "ad2antrr.mm"
include "syl2anc.mm"
include "ex.mm"
include "f1oeq1.mm"
include "elab.mm"
include "coex.mm"
include "cnvex.mm"
include "3imtr4g.mm"
include "ad2antlr.mm"
include "ancoms.mm"
include "adantlr.mm"
include "anbi12i.mm"
include "coass.mm"
include "cid.mm"
include "cres.mm"
include "f1ococnv1.mm"
include "coeq2d.mm"
include "adantrr.mm"
include "fcoi1.mm"
include "3syl.mm"
include "eqtrd.mm"
include "syl5req.mm"
include "f1ococnv2.mm"
include "coeq1d.mm"
include "adantrl.mm"
include "fcoi2.mm"
include "syl5eqr.mm"
include "eqeq12d.mm"
include "eqcom.mm"
include "syl6bb.mm"
include "wf1.mm"
include "f1of1.mm"
include "ad2antrl.mm"
include "cocan1.mm"
include "syl3anc.mm"
include "wfn.mm"
include "f1ofn.mm"
include "ad2antll.mm"
include "cocan2.mm"
include "3bitr3d.mm"
include "syl5bi.mm"
include "en3d.mm"
include "exlimivv.mm"
include "sylbir.mm"
include "syl2anb.mm"

theorem hashfacen
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D
  let vf: setvar f
  let vg: setvar g
  let vh: setvar h
  let vx: setvar x
  let vy: setvar y

  disjoint A f
  disjoint B f
  disjoint C f
  disjoint D f
  disjoint f g
  disjoint f h
  disjoint f x
  disjoint f y
  disjoint g h
  disjoint g x
  disjoint g y
  disjoint A g
  disjoint h x
  disjoint h y
  disjoint A h
  disjoint x y
  disjoint A x
  disjoint A y
  disjoint B g
  disjoint B h
  disjoint B x
  disjoint B y
  disjoint C g
  disjoint C h
  disjoint C x
  disjoint C y
  disjoint D g
  disjoint D h
  disjoint D x
  disjoint D y
  assert |- ( ( A ~~ B /\ C ~~ D ) -> { f | f : A -1-1-onto-> C } ~~ { f | f : B -1-1-onto-> D } )

  proof
    cA
    cB
    cen
    wbr
    cA
    cB
    vg
    cv
    #
    wf1o
    #
    vg
    wex
    #
    cC
    cD
    vh
    cv
    #
    wf1o
    #
    vh
    wex
    #
    cA
    cC
    vf
    cv
    #
    wf1o
    #
    vf
    cab
    #
    cB
    cD
    @6
    wf1o
    #
    vf
    cab
    #
    cen
    wbr
    #
    cC
    cD
    cen
    wbr
    cA
    cB
    vg
    bren
    cC
    cD
    vh
    bren
    @2
    @5
    wa
    @1
    @4
    wa
    #
    vh
    wex
    vg
    wex
    @11
    @1
    @4
    vg
    vh
    eeanv
    @12
    @11
    vg
    vh
    @12
    vx
    vy
    @8
    @10
    @3
    vx
    cv
    #
    ccom
    #
    @0
    ccnv
    #
    ccom
    #
    @3
    ccnv
    #
    vy
    cv
    #
    @0
    ccom
    #
    ccom
    #
    @12
    @8
    cC
    cA
    cmap
    co
    #
    wss
    @8
    cvv
    wcel
    @12
    @7
    vf
    @21
    @7
    @6
    @21
    wcel
    #
    @12
    cA
    cC
    @6
    wf
    #
    cA
    cC
    @6
    f1of
    @4
    cC
    cvv
    wcel
    cA
    cvv
    wcel
    @22
    @23
    wb
    @1
    @4
    cC
    @3
    cdm
    cvv
    cC
    cD
    @3
    f1odm
    @3
    vh
    vex
    #
    dmex
    syl6eqelr
    @1
    cA
    @0
    cdm
    cvv
    cA
    cB
    @0
    f1odm
    @0
    vg
    vex
    #
    dmex
    syl6eqelr
    cC
    cA
    @6
    cvv
    cvv
    elmapg
    syl2anr
    syl5ibr
    abssdv
    @8
    @21
    cC
    cA
    cmap
    ovex
    ssex
    syl
    @12
    @10
    cD
    cB
    cmap
    co
    #
    wss
    @10
    cvv
    wcel
    @12
    @9
    vf
    @26
    @9
    @6
    @26
    wcel
    #
    @12
    cB
    cD
    @6
    wf
    #
    cB
    cD
    @6
    f1of
    @4
    cD
    cvv
    wcel
    cB
    cvv
    wcel
    @27
    @28
    wb
    @1
    @4
    cD
    @3
    crn
    #
    cvv
    @4
    cC
    cD
    @3
    wfo
    @29
    cD
    wceq
    cC
    cD
    @3
    f1ofo
    cC
    cD
    @3
    forn
    syl
    @3
    @24
    rnex
    syl6eqelr
    @1
    cB
    @0
    crn
    #
    cvv
    @1
    cA
    cB
    @0
    wfo
    #
    @30
    cB
    wceq
    cA
    cB
    @0
    f1ofo
    #
    cA
    cB
    @0
    forn
    syl
    @0
    @25
    rnex
    syl6eqelr
    cD
    cB
    @6
    cvv
    cvv
    elmapg
    syl2anr
    syl5ibr
    abssdv
    @10
    @26
    cD
    cB
    cmap
    ovex
    ssex
    syl
    @12
    cA
    cC
    @13
    wf1o
    #
    cB
    cD
    @16
    wf1o
    #
    @13
    @8
    wcel
    #
    @16
    @10
    wcel
    @12
    @33
    @34
    @12
    @33
    wa
    cA
    cD
    @14
    wf1o
    #
    cB
    cA
    @15
    wf1o
    #
    @34
    @4
    @33
    @36
    @1
    cA
    cC
    cD
    @3
    @13
    f1oco
    adantll
    #
    @1
    @37
    @4
    @33
    cA
    cB
    @0
    f1ocnv
    ad2antrr
    cB
    cA
    cD
    @14
    @15
    f1oco
    syl2anc
    #
    ex
    @7
    @33
    vf
    @13
    vx
    vex
    #
    cA
    cC
    @6
    @13
    f1oeq1
    elab
    #
    @9
    @34
    vf
    @16
    @14
    @15
    @3
    @13
    @24
    @40
    coex
    @0
    @25
    cnvex
    coex
    cB
    cD
    @6
    @16
    f1oeq1
    elab
    3imtr4g
    @12
    cB
    cD
    @18
    wf1o
    #
    cA
    cC
    @20
    wf1o
    #
    @18
    @10
    wcel
    #
    @20
    @8
    wcel
    @12
    @42
    @43
    @12
    @42
    wa
    cD
    cC
    @17
    wf1o
    #
    cA
    cD
    @19
    wf1o
    #
    @43
    @4
    @45
    @1
    @42
    cC
    cD
    @3
    f1ocnv
    ad2antlr
    @1
    @42
    @46
    @4
    @42
    @1
    @46
    cA
    cB
    cD
    @18
    @0
    f1oco
    ancoms
    adantlr
    #
    cA
    cD
    cC
    @17
    @19
    f1oco
    syl2anc
    #
    ex
    @9
    @42
    vf
    @18
    vy
    vex
    #
    cB
    cD
    @6
    @18
    f1oeq1
    elab
    #
    @7
    @43
    vf
    @20
    @17
    @19
    @3
    @24
    cnvex
    @18
    @0
    @49
    @25
    coex
    coex
    cA
    cC
    @6
    @20
    f1oeq1
    elab
    3imtr4g
    @35
    @44
    wa
    @33
    @42
    wa
    #
    @12
    @13
    @20
    wceq
    #
    @18
    @16
    wceq
    #
    wb
    #
    @35
    @33
    @44
    @42
    @41
    @50
    anbi12i
    @12
    @51
    @54
    @12
    @51
    wa
    #
    @14
    @3
    @20
    ccom
    #
    wceq
    #
    @19
    @16
    @0
    ccom
    #
    wceq
    #
    @52
    @53
    @55
    @57
    @58
    @19
    wceq
    @59
    @55
    @14
    @58
    @56
    @19
    @55
    @58
    @14
    @15
    @0
    ccom
    #
    ccom
    #
    @14
    @14
    @15
    @0
    coass
    @55
    @61
    @14
    cid
    cA
    cres
    #
    ccom
    #
    @14
    @55
    @60
    @62
    @14
    @1
    @60
    @62
    wceq
    @4
    @51
    cA
    cB
    @0
    f1ococnv1
    ad2antrr
    coeq2d
    @55
    @36
    cA
    cD
    @14
    wf
    @63
    @14
    wceq
    @12
    @33
    @36
    @42
    @38
    adantrr
    cA
    cD
    @14
    f1of
    cA
    cD
    @14
    fcoi1
    3syl
    eqtrd
    syl5req
    @55
    @56
    @3
    @17
    ccom
    #
    @19
    ccom
    #
    @19
    @3
    @17
    @19
    coass
    @55
    @65
    cid
    cD
    cres
    #
    @19
    ccom
    #
    @19
    @55
    @64
    @66
    @19
    @4
    @64
    @66
    wceq
    @1
    @51
    cC
    cD
    @3
    f1ococnv2
    ad2antlr
    coeq1d
    @55
    @46
    cA
    cD
    @19
    wf
    @67
    @19
    wceq
    @12
    @42
    @46
    @33
    @47
    adantrl
    cA
    cD
    @19
    f1of
    cA
    cD
    @19
    fcoi2
    3syl
    eqtrd
    syl5eqr
    eqeq12d
    @58
    @19
    eqcom
    syl6bb
    @55
    cC
    cD
    @3
    wf1
    #
    cA
    cC
    @13
    wf
    #
    cA
    cC
    @20
    wf
    #
    @57
    @52
    wb
    @4
    @68
    @1
    @51
    cC
    cD
    @3
    f1of1
    ad2antlr
    @33
    @69
    @12
    @42
    cA
    cC
    @13
    f1of
    ad2antrl
    @55
    @43
    @70
    @12
    @42
    @43
    @33
    @48
    adantrl
    cA
    cC
    @20
    f1of
    syl
    cA
    cC
    cD
    @3
    @13
    @20
    cocan1
    syl3anc
    @55
    @31
    @18
    cB
    wfn
    #
    @16
    cB
    wfn
    #
    @59
    @53
    wb
    @1
    @31
    @4
    @51
    @32
    ad2antrr
    @42
    @71
    @12
    @33
    cB
    cD
    @18
    f1ofn
    ad2antll
    @55
    @34
    @72
    @12
    @33
    @34
    @42
    @39
    adantrr
    cB
    cD
    @16
    f1ofn
    syl
    cA
    cB
    @0
    @18
    @16
    cocan2
    syl3anc
    3bitr3d
    ex
    syl5bi
    en3d
    exlimivv
    sylbir
    syl2anb
end
