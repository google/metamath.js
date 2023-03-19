include "cply.mm"
include "cfv.mm"
include "wcel.mm"
include "c0p.mm"
include "wne.mm"
include "w3a.mm"
include "cquot.mm"
include "co.mm"
include "cmin.mm"
include "cof.mm"
include "cc.mm"
include "cc0.mm"
include "csn.mm"
include "cxp.mm"
include "wceq.mm"
include "cmul.mm"
include "cdgr.mm"
include "clt.mm"
include "wbr.mm"
include "wo.mm"
include "wb.mm"
include "plyssc.mm"
include "simp2.mm"
include "sseldi.mm"
include "simp1.mm"
include "wa.mm"
include "plymulcl.mm"
include "syl5eqel.mm"
include "3adant3.mm"
include "simp3.mm"
include "quotcl2.mm"
include "syl3anc.mm"
include "plysubcl.mm"
include "syl2anc.mm"
include "plymul0or.mm"
include "cvv.mm"
include "cnex.mm"
include "a1i.mm"
include "wf.mm"
include "plyf.mm"
include "syl.mm"
include "cv.mm"
include "mulcom.mm"
include "adantl.mm"
include "caofcom.mm"
include "syl5eq.mm"
include "oveq1d.mm"
include "subdi.mm"
include "caofdi.mm"
include "eqtr4d.mm"
include "eqeq1d.mm"
include "wn.mm"
include "neneqd.mm"
include "biorf.mm"
include "3bitr4d.mm"
include "biimpd.mm"
include "cle.mm"
include "caddc.mm"
include "wi.mm"
include "eqid.mm"
include "dgrmul.mm"
include "expr.mm"
include "syl21anc.mm"
include "cr.mm"
include "cn0.mm"
include "dgrcl.mm"
include "nn0red.mm"
include "nn0addge1.mm"
include "breq2.mm"
include "syl5ibrcom.mm"
include "syld.mm"
include "fveq2d.mm"
include "breq2d.mm"
include "lenltd.mm"
include "bitr3d.mm"
include "sylibd.mm"
include "necon4ad.mm"
include "quotdgr.mm"
include "mpjaod.mm"
include "df-0p.mm"
include "syl6eq.mm"
include "ofsubeq0.mm"
include "mpbid.mm"
include "eqcomd.mm"

theorem quotcan
  let cS: class S
  let cF: class F
  let cG: class G
  let cH: class H
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  assume quotcan.1: |- H = ( F oF x. G )


  assert |- ( ( F e. ( Poly ` S ) /\ G e. ( Poly ` S ) /\ G =/= 0p ) -> ( H quot G ) = F )

  proof
    cF
    cS
    cply
    cfv
    #
    wcel
    #
    cG
    @0
    wcel
    #
    cG
    c0p
    wne
    #
    w3a
    #
    cF
    cH
    cG
    cquot
    co
    #
    @4
    cF
    @5
    cmin
    cof
    #
    co
    #
    cc
    cc0
    csn
    cxp
    #
    wceq
    #
    cF
    @5
    wceq
    #
    @4
    @7
    c0p
    @8
    @4
    cH
    cG
    @5
    cmul
    cof
    #
    co
    #
    @6
    co
    #
    c0p
    wceq
    #
    @7
    c0p
    wceq
    #
    @13
    cdgr
    cfv
    #
    cG
    cdgr
    cfv
    #
    clt
    wbr
    #
    @4
    @14
    @15
    @4
    cG
    @7
    @11
    co
    #
    c0p
    wceq
    #
    cG
    c0p
    wceq
    #
    @15
    wo
    #
    @14
    @15
    @4
    cG
    cc
    cply
    cfv
    #
    wcel
    #
    @7
    @23
    wcel
    #
    @20
    @22
    wb
    @4
    @0
    @23
    cG
    cS
    plyssc
    #
    @1
    @2
    @3
    simp2
    #
    sseldi
    #
    @4
    cF
    @23
    wcel
    @5
    @23
    wcel
    #
    @25
    @4
    @0
    @23
    cF
    @26
    @1
    @2
    @3
    simp1
    #
    sseldi
    @4
    cH
    @23
    wcel
    #
    @24
    @3
    @29
    @1
    @2
    @31
    @3
    @1
    @2
    wa
    cH
    cF
    cG
    @11
    co
    #
    @23
    quotcan.1
    cS
    cF
    cG
    plymulcl
    syl5eqel
    3adant3
    #
    @28
    @1
    @2
    @3
    simp3
    #
    cc
    cH
    cG
    quotcl2
    syl3anc
    #
    cc
    cF
    @5
    plysubcl
    syl2anc
    #
    cc
    cG
    @7
    plymul0or
    syl2anc
    @4
    @13
    @19
    c0p
    @4
    @13
    cG
    cF
    @11
    co
    #
    @12
    @6
    co
    @19
    @4
    cH
    @37
    @12
    @6
    @4
    cH
    @32
    @37
    quotcan.1
    @4
    vx
    vy
    cc
    cmul
    cc
    cF
    cG
    cvv
    cc
    cvv
    wcel
    #
    @4
    cnex
    a1i
    #
    @4
    @1
    cc
    cc
    cF
    wf
    #
    @30
    cS
    cF
    plyf
    syl
    #
    @4
    @2
    cc
    cc
    cG
    wf
    @27
    cS
    cG
    plyf
    syl
    #
    vx
    cv
    #
    cc
    wcel
    #
    vy
    cv
    #
    cc
    wcel
    #
    wa
    @43
    @45
    cmul
    co
    #
    @45
    @43
    cmul
    co
    wceq
    @4
    @43
    @45
    mulcom
    adantl
    caofcom
    syl5eq
    oveq1d
    @4
    vx
    vy
    vz
    cc
    cmin
    cc
    cmul
    cG
    cF
    @5
    cc
    cmin
    cvv
    @39
    @42
    @41
    @4
    @29
    cc
    cc
    @5
    wf
    #
    @35
    cc
    @5
    plyf
    syl
    #
    @44
    @46
    vz
    cv
    #
    cc
    wcel
    w3a
    @43
    @45
    @50
    cmin
    co
    cmul
    co
    @47
    @43
    @50
    cmul
    co
    cmin
    co
    wceq
    @4
    @43
    @45
    @50
    subdi
    adantl
    caofdi
    eqtr4d
    #
    eqeq1d
    @4
    @21
    wn
    @15
    @22
    wb
    @4
    cG
    c0p
    @34
    neneqd
    @21
    @15
    biorf
    syl
    3bitr4d
    biimpd
    @4
    @18
    @7
    c0p
    @4
    @7
    c0p
    wne
    #
    @17
    @19
    cdgr
    cfv
    #
    cle
    wbr
    #
    @18
    wn
    #
    @4
    @52
    @53
    @17
    @7
    cdgr
    cfv
    #
    caddc
    co
    #
    wceq
    #
    @54
    @4
    @24
    @3
    @25
    @52
    @58
    wi
    @28
    @34
    @36
    @24
    @3
    wa
    @25
    @52
    @58
    cc
    cG
    @7
    @17
    @56
    @17
    eqid
    @56
    eqid
    dgrmul
    expr
    syl21anc
    @4
    @54
    @58
    @17
    @57
    cle
    wbr
    #
    @4
    @17
    cr
    wcel
    @56
    cn0
    wcel
    #
    @59
    @4
    @17
    @4
    @2
    @17
    cn0
    wcel
    @27
    cS
    cG
    dgrcl
    syl
    nn0red
    #
    @4
    @25
    @60
    @36
    cc
    @7
    dgrcl
    syl
    @17
    @56
    nn0addge1
    syl2anc
    @53
    @57
    @17
    cle
    breq2
    syl5ibrcom
    syld
    @4
    @17
    @16
    cle
    wbr
    @54
    @55
    @4
    @16
    @53
    @17
    cle
    @4
    @13
    @19
    cdgr
    @51
    fveq2d
    breq2d
    @4
    @17
    @16
    @61
    @4
    @16
    @4
    @13
    @23
    wcel
    #
    @16
    cn0
    wcel
    @4
    @31
    @12
    @23
    wcel
    #
    @62
    @33
    @4
    @24
    @29
    @63
    @28
    @35
    cc
    cG
    @5
    plymulcl
    syl2anc
    cc
    cH
    @12
    plysubcl
    syl2anc
    cc
    @13
    dgrcl
    syl
    nn0red
    lenltd
    bitr3d
    sylibd
    necon4ad
    @4
    @31
    @24
    @3
    @14
    @18
    wo
    @33
    @28
    @34
    @13
    cc
    cH
    cG
    @13
    eqid
    quotdgr
    syl3anc
    mpjaod
    df-0p
    syl6eq
    @4
    @38
    @40
    @48
    @9
    @10
    wb
    @39
    @41
    @49
    cc
    cF
    @5
    cvv
    ofsubeq0
    syl3anc
    mpbid
    eqcomd
end
