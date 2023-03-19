include "c0.mm"
include "wne.mm"
include "cpsmet.mm"
include "cfv.mm"
include "wcel.mm"
include "wa.mm"
include "cmetu.mm"
include "cxp.mm"
include "wss.mm"
include "cv.mm"
include "crp.mm"
include "ccnv.mm"
include "cc0.mm"
include "cico.mm"
include "co.mm"
include "cima.mm"
include "cmpt.mm"
include "crn.mm"
include "wrex.mm"
include "clt.mm"
include "wbr.mm"
include "wi.mm"
include "wral.mm"
include "wb.mm"
include "eleq2i.mm"
include "a1i.mm"
include "metuel.mm"
include "wceq.mm"
include "wex.mm"
include "cvv.mm"
include "vex.mm"
include "oveq2.mm"
include "imaeq2d.mm"
include "cbvmptv.mm"
include "elrnmpt.mm"
include "ax-mp.mm"
include "anbi1i.mm"
include "r19.41v.mm"
include "bitr4i.mm"
include "exbii.mm"
include "df-rex.mm"
include "rexcom4.mm"
include "3bitr4i.mm"
include "cnvexg.mm"
include "imaexg.mm"
include "sseq1.mm"
include "ceqsexgv.mm"
include "3syl.mm"
include "rexbidv.mm"
include "adantr.mm"
include "syl5bb.mm"
include "cop.mm"
include "cdm.mm"
include "cnvimass.mm"
include "cxr.mm"
include "wf.mm"
include "simpll.mm"
include "psmetf.mm"
include "fdm.mm"
include "syl5sseq.mm"
include "ssrel2.mm"
include "syl.mm"
include "simplr.mm"
include "simpr.mm"
include "opelxp.mm"
include "sylanbrc.mm"
include "biantrurd.mm"
include "cle.mm"
include "w3a.mm"
include "simp-4l.mm"
include "psmetcl.mm"
include "syl3anc.mm"
include "3biant1d.mm"
include "psmetge0.mm"
include "0xr.mm"
include "simpllr.mm"
include "rpxrd.mm"
include "elico1.mm"
include "sylancr.mm"
include "3bitr4d.mm"
include "df-ov.mm"
include "eleq1i.mm"
include "syl6bb.mm"
include "wfn.mm"
include "ffn.mm"
include "elpreima.mm"
include "4syl.mm"
include "anasss.mm"
include "df-br.mm"
include "imbi12d.mm"
include "2ralbidva.mm"
include "bitr4d.mm"
include "rexbidva.mm"
include "bitrd.mm"
include "pm5.32da.mm"
include "adantl.mm"
include "3bitrd.mm"

theorem metuel2
  let vx: setvar x
  let vy: setvar y
  let cD: class D
  let cU: class U
  let cV: class V
  let cX: class X
  let vd: setvar d
  let va: setvar a
  let vw: setvar w
  assume metuel2.u: |- U = ( metUnif ` D )

  disjoint d x
  disjoint d y
  disjoint D d
  disjoint x y
  disjoint D x
  disjoint D y
  disjoint V d
  disjoint V x
  disjoint V y
  disjoint X d
  disjoint X x
  disjoint X y
  disjoint a d
  disjoint a w
  disjoint a x
  disjoint a y
  disjoint D a
  disjoint d w
  disjoint w x
  disjoint w y
  disjoint D w
  disjoint V w
  disjoint X a
  assert |- ( ( X =/= (/) /\ D e. ( PsMet ` X ) ) -> ( V e. U <-> ( V C_ ( X X. X ) /\ E. d e. RR+ A. x e. X A. y e. X ( ( x D y ) < d -> x V y ) ) ) )

  proof
    cX
    c0
    wne
    #
    cD
    cX
    cpsmet
    cfv
    #
    wcel
    #
    wa
    #
    cV
    cU
    wcel
    #
    cV
    cD
    cmetu
    cfv
    #
    wcel
    #
    cV
    cX
    cX
    cxp
    #
    wss
    #
    vw
    cv
    #
    cV
    wss
    #
    vw
    va
    crp
    cD
    ccnv
    #
    cc0
    va
    cv
    #
    cico
    co
    #
    cima
    #
    cmpt
    #
    crn
    #
    wrex
    #
    wa
    #
    @8
    vx
    cv
    #
    vy
    cv
    #
    cD
    co
    #
    vd
    cv
    #
    clt
    wbr
    #
    @19
    @20
    cV
    wbr
    #
    wi
    #
    vy
    cX
    wral
    vx
    cX
    wral
    #
    vd
    crp
    wrex
    #
    wa
    #
    @4
    @6
    wb
    @3
    cU
    @5
    cV
    metuel2.u
    eleq2i
    a1i
    vw
    cD
    cV
    cX
    va
    metuel
    @2
    @18
    @28
    wb
    @0
    @2
    @8
    @17
    @27
    @2
    @8
    wa
    #
    @17
    @11
    cc0
    @22
    cico
    co
    #
    cima
    #
    cV
    wss
    #
    vd
    crp
    wrex
    #
    @27
    @17
    @9
    @31
    wceq
    #
    @10
    wa
    #
    vw
    wex
    #
    vd
    crp
    wrex
    #
    @29
    @33
    @9
    @16
    wcel
    #
    @10
    wa
    #
    vw
    wex
    @35
    vd
    crp
    wrex
    #
    vw
    wex
    @17
    @37
    @39
    @40
    vw
    @39
    @34
    vd
    crp
    wrex
    #
    @10
    wa
    @40
    @38
    @41
    @10
    @9
    cvv
    wcel
    @38
    @41
    wb
    vw
    vex
    vd
    crp
    @31
    @9
    @15
    cvv
    va
    vd
    crp
    @14
    @31
    @12
    @22
    wceq
    @13
    @30
    @11
    @12
    @22
    cc0
    cico
    oveq2
    imaeq2d
    cbvmptv
    elrnmpt
    ax-mp
    anbi1i
    @34
    @10
    vd
    crp
    r19.41v
    bitr4i
    exbii
    @10
    vw
    @16
    df-rex
    @35
    vd
    vw
    crp
    rexcom4
    3bitr4i
    @2
    @37
    @33
    wb
    @8
    @2
    @36
    @32
    vd
    crp
    @2
    @11
    cvv
    wcel
    @31
    cvv
    wcel
    @36
    @32
    wb
    cD
    @1
    cnvexg
    @11
    @30
    cvv
    imaexg
    @10
    @32
    vw
    @31
    cvv
    @9
    @31
    cV
    sseq1
    ceqsexgv
    3syl
    rexbidv
    adantr
    syl5bb
    @29
    @32
    @26
    vd
    crp
    @29
    @22
    crp
    wcel
    #
    wa
    #
    @32
    @19
    @20
    cop
    #
    @31
    wcel
    #
    @44
    cV
    wcel
    #
    wi
    #
    vy
    cX
    wral
    vx
    cX
    wral
    #
    @26
    @43
    @31
    @7
    wss
    @32
    @48
    wb
    @43
    cD
    cdm
    #
    @31
    @7
    cD
    @30
    cnvimass
    @43
    @2
    @7
    cxr
    cD
    wf
    #
    @49
    @7
    wceq
    @2
    @8
    @42
    simpll
    cD
    cX
    psmetf
    #
    @7
    cxr
    cD
    fdm
    3syl
    syl5sseq
    vx
    vy
    cX
    cX
    @31
    cV
    ssrel2
    syl
    @43
    @25
    @47
    vx
    vy
    cX
    cX
    @43
    @19
    cX
    wcel
    #
    @20
    cX
    wcel
    #
    wa
    wa
    #
    @23
    @45
    @24
    @46
    @43
    @52
    @53
    @23
    @45
    wb
    @43
    @52
    wa
    #
    @53
    wa
    #
    @44
    cD
    cfv
    #
    @30
    wcel
    #
    @44
    @7
    wcel
    #
    @58
    wa
    #
    @23
    @45
    @56
    @59
    @58
    @56
    @52
    @53
    @59
    @43
    @52
    @53
    simplr
    #
    @55
    @53
    simpr
    #
    @19
    @20
    cX
    cX
    opelxp
    sylanbrc
    biantrurd
    @56
    @23
    @21
    @30
    wcel
    #
    @58
    @56
    cc0
    @21
    cle
    wbr
    #
    @23
    wa
    #
    @21
    cxr
    wcel
    #
    @64
    @23
    w3a
    #
    @23
    @63
    @56
    @23
    @64
    @66
    @56
    @2
    @52
    @53
    @66
    @2
    @8
    @42
    @52
    @53
    simp-4l
    #
    @61
    @62
    @19
    @20
    cD
    cX
    psmetcl
    syl3anc
    3biant1d
    @56
    @2
    @52
    @53
    @23
    @65
    wb
    @68
    @61
    @62
    @2
    @52
    @53
    w3a
    @64
    @23
    @19
    @20
    cD
    cX
    psmetge0
    biantrurd
    syl3anc
    @56
    cc0
    cxr
    wcel
    @22
    cxr
    wcel
    @63
    @67
    wb
    0xr
    @56
    @22
    @29
    @42
    @52
    @53
    simpllr
    rpxrd
    cc0
    @22
    @21
    elico1
    sylancr
    3bitr4d
    @21
    @57
    @30
    @19
    @20
    cD
    df-ov
    eleq1i
    syl6bb
    @56
    @2
    @50
    cD
    @7
    wfn
    @45
    @60
    wb
    @68
    @51
    @7
    cxr
    cD
    ffn
    @7
    @44
    @30
    cD
    elpreima
    4syl
    3bitr4d
    anasss
    @24
    @46
    wb
    @54
    @19
    @20
    cV
    df-br
    a1i
    imbi12d
    2ralbidva
    bitr4d
    rexbidva
    bitrd
    pm5.32da
    adantl
    3bitrd
end
