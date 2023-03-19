include "cen.mm"
include "wbr.mm"
include "cv.mm"
include "wf1o.mm"
include "wex.mm"
include "cmap.mm"
include "co.mm"
include "bren.mm"
include "wa.mm"
include "eeanv.mm"
include "ccom.mm"
include "ccnv.mm"
include "ovexd.mm"
include "wcel.mm"
include "wf.mm"
include "elmapi.mm"
include "f1of.mm"
include "adantr.mm"
include "fco.mm"
include "sylan.mm"
include "f1ocnv.mm"
include "adantl.mm"
include "syl.mm"
include "syl2anc.mm"
include "ex.mm"
include "syl5.mm"
include "cvv.mm"
include "crn.mm"
include "wfo.mm"
include "wceq.mm"
include "f1ofo.mm"
include "forn.mm"
include "vex.mm"
include "rnex.mm"
include "syl6eqelr.mm"
include "elmapd.mm"
include "sylibrd.mm"
include "id.mm"
include "syl2anr.mm"
include "cdm.mm"
include "f1odm.mm"
include "dmex.mm"
include "wb.mm"
include "coass.mm"
include "cid.mm"
include "cres.mm"
include "f1ococnv2.mm"
include "ad2antrr.mm"
include "coeq1d.mm"
include "adantrl.mm"
include "fcoi2.mm"
include "eqtrd.mm"
include "syl5eqr.mm"
include "eqeq2d.mm"
include "f1ococnv1.mm"
include "ad2antlr.mm"
include "coeq2d.mm"
include "adantrr.mm"
include "fcoi1.mm"
include "syl5eq.mm"
include "eqcom.mm"
include "syl6bb.mm"
include "bitr4d.mm"
include "wf1.mm"
include "f1of1.mm"
include "simprl.mm"
include "cocan1.mm"
include "syl3anc.mm"
include "wfn.mm"
include "ffn.mm"
include "ad2antll.mm"
include "cocan2.mm"
include "3bitr3d.mm"
include "syl2ani.mm"
include "en3d.mm"
include "exlimivv.mm"
include "sylbir.mm"
include "syl2anb.mm"

theorem mapen
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D
  let vf: setvar f
  let vg: setvar g
  let vx: setvar x
  let vy: setvar y


  assert |- ( ( A ~~ B /\ C ~~ D ) -> ( A ^m C ) ~~ ( B ^m D ) )

  proof
    cA
    cB
    cen
    wbr
    cA
    cB
    vf
    cv
    #
    wf1o
    #
    vf
    wex
    #
    cC
    cD
    vg
    cv
    #
    wf1o
    #
    vg
    wex
    #
    cA
    cC
    cmap
    co
    #
    cB
    cD
    cmap
    co
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
    vf
    bren
    cC
    cD
    vg
    bren
    @2
    @5
    wa
    @1
    @4
    wa
    #
    vg
    wex
    vf
    wex
    @8
    @1
    @4
    vf
    vg
    eeanv
    @9
    @8
    vf
    vg
    @9
    vx
    vy
    @6
    @7
    @0
    vx
    cv
    #
    ccom
    #
    @3
    ccnv
    #
    ccom
    #
    @0
    ccnv
    #
    vy
    cv
    #
    @3
    ccom
    #
    ccom
    #
    @9
    cA
    cC
    cmap
    ovexd
    @9
    cB
    cD
    cmap
    ovexd
    @9
    @10
    @6
    wcel
    #
    cD
    cB
    @13
    wf
    #
    @13
    @7
    wcel
    @18
    cC
    cA
    @10
    wf
    #
    @9
    @19
    @10
    cA
    cC
    elmapi
    #
    @9
    @20
    @19
    @9
    @20
    wa
    cC
    cB
    @11
    wf
    #
    cD
    cC
    @12
    wf
    #
    @19
    @9
    cA
    cB
    @0
    wf
    #
    @20
    @22
    @1
    @24
    @4
    cA
    cB
    @0
    f1of
    adantr
    cC
    cA
    cB
    @0
    @10
    fco
    sylan
    #
    @9
    @23
    @20
    @9
    cD
    cC
    @12
    wf1o
    #
    @23
    @4
    @26
    @1
    cC
    cD
    @3
    f1ocnv
    adantl
    cD
    cC
    @12
    f1of
    syl
    adantr
    cD
    cC
    cB
    @11
    @12
    fco
    syl2anc
    #
    ex
    syl5
    @9
    cB
    cD
    @13
    cvv
    cvv
    @9
    cB
    @0
    crn
    #
    cvv
    @9
    cA
    cB
    @0
    wfo
    #
    @28
    cB
    wceq
    @1
    @29
    @4
    cA
    cB
    @0
    f1ofo
    adantr
    cA
    cB
    @0
    forn
    syl
    @0
    vf
    vex
    #
    rnex
    syl6eqelr
    @9
    cD
    @3
    crn
    #
    cvv
    @9
    cC
    cD
    @3
    wfo
    #
    @31
    cD
    wceq
    @4
    @32
    @1
    cC
    cD
    @3
    f1ofo
    adantl
    #
    cC
    cD
    @3
    forn
    syl
    @3
    vg
    vex
    #
    rnex
    syl6eqelr
    elmapd
    sylibrd
    @9
    @15
    @7
    wcel
    #
    cC
    cA
    @17
    wf
    #
    @17
    @6
    wcel
    @35
    cD
    cB
    @15
    wf
    #
    @9
    @36
    @15
    cB
    cD
    elmapi
    #
    @9
    @37
    @36
    @9
    @37
    wa
    cB
    cA
    @14
    wf
    #
    cC
    cB
    @16
    wf
    #
    @36
    @9
    @39
    @37
    @9
    cB
    cA
    @14
    wf1o
    #
    @39
    @1
    @41
    @4
    cA
    cB
    @0
    f1ocnv
    adantr
    cB
    cA
    @14
    f1of
    syl
    adantr
    @37
    @37
    cC
    cD
    @3
    wf
    #
    @40
    @9
    @37
    id
    @4
    @42
    @1
    cC
    cD
    @3
    f1of
    adantl
    cC
    cD
    cB
    @15
    @3
    fco
    syl2anr
    #
    cC
    cB
    cA
    @14
    @16
    fco
    syl2anc
    #
    ex
    syl5
    @9
    cA
    cC
    @17
    cvv
    cvv
    @9
    cA
    @0
    cdm
    #
    cvv
    @1
    @45
    cA
    wceq
    @4
    cA
    cB
    @0
    f1odm
    adantr
    @0
    @30
    dmex
    syl6eqelr
    @9
    cC
    @3
    cdm
    #
    cvv
    @4
    @46
    cC
    wceq
    @1
    cC
    cD
    @3
    f1odm
    adantl
    @3
    @34
    dmex
    syl6eqelr
    elmapd
    sylibrd
    @18
    @9
    @20
    @37
    @10
    @17
    wceq
    #
    @15
    @13
    wceq
    #
    wb
    #
    @35
    @21
    @38
    @9
    @20
    @37
    wa
    #
    @49
    @9
    @50
    wa
    #
    @11
    @0
    @17
    ccom
    #
    wceq
    #
    @16
    @13
    @3
    ccom
    #
    wceq
    #
    @47
    @48
    @51
    @53
    @11
    @16
    wceq
    #
    @55
    @51
    @52
    @16
    @11
    @51
    @52
    @0
    @14
    ccom
    #
    @16
    ccom
    #
    @16
    @0
    @14
    @16
    coass
    @51
    @58
    cid
    cB
    cres
    #
    @16
    ccom
    #
    @16
    @51
    @57
    @59
    @16
    @1
    @57
    @59
    wceq
    @4
    @50
    cA
    cB
    @0
    f1ococnv2
    ad2antrr
    coeq1d
    @51
    @40
    @60
    @16
    wceq
    @9
    @37
    @40
    @20
    @43
    adantrl
    cC
    cB
    @16
    fcoi2
    syl
    eqtrd
    syl5eqr
    eqeq2d
    @51
    @55
    @16
    @11
    wceq
    @56
    @51
    @54
    @11
    @16
    @51
    @54
    @11
    @12
    @3
    ccom
    #
    ccom
    #
    @11
    @11
    @12
    @3
    coass
    @51
    @62
    @11
    cid
    cC
    cres
    #
    ccom
    #
    @11
    @51
    @61
    @63
    @11
    @4
    @61
    @63
    wceq
    @1
    @50
    cC
    cD
    @3
    f1ococnv1
    ad2antlr
    coeq2d
    @51
    @22
    @64
    @11
    wceq
    @9
    @20
    @22
    @37
    @25
    adantrr
    cC
    cB
    @11
    fcoi1
    syl
    eqtrd
    syl5eq
    eqeq2d
    @16
    @11
    eqcom
    syl6bb
    bitr4d
    @51
    cA
    cB
    @0
    wf1
    #
    @20
    @36
    @53
    @47
    wb
    @1
    @65
    @4
    @50
    cA
    cB
    @0
    f1of1
    ad2antrr
    @9
    @20
    @37
    simprl
    @9
    @37
    @36
    @20
    @44
    adantrl
    cC
    cA
    cB
    @0
    @10
    @17
    cocan1
    syl3anc
    @51
    @32
    @15
    cD
    wfn
    #
    @13
    cD
    wfn
    #
    @55
    @48
    wb
    @9
    @32
    @50
    @33
    adantr
    @37
    @66
    @9
    @20
    cD
    cB
    @15
    ffn
    ad2antll
    @51
    @19
    @67
    @9
    @20
    @19
    @37
    @27
    adantrr
    cD
    cB
    @13
    ffn
    syl
    cC
    cD
    @3
    @15
    @13
    cocan2
    syl3anc
    3bitr3d
    ex
    syl2ani
    en3d
    exlimivv
    sylbir
    syl2anb
end
