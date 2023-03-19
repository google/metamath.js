include "cstr.mm"
include "wbr.mm"
include "cvv.mm"
include "wcel.mm"
include "wa.mm"
include "cle.mm"
include "cn.mm"
include "cxp.mm"
include "cin.mm"
include "c0.mm"
include "csn.mm"
include "cdif.mm"
include "wfun.mm"
include "cdm.mm"
include "cfz.mm"
include "cfv.mm"
include "wss.mm"
include "w3a.mm"
include "wrel.mm"
include "brstruct.mm"
include "brrelex12.mm"
include "mpan.mm"
include "cun.mm"
include "ssun1.mm"
include "undif1.mm"
include "sseqtr4i.mm"
include "cfn.mm"
include "wfn.mm"
include "simp2.mm"
include "funfn.mm"
include "sylib.mm"
include "c1st.mm"
include "c2nd.mm"
include "cop.mm"
include "wceq.mm"
include "inss2.mm"
include "sseli.mm"
include "1st2nd2.mm"
include "syl.mm"
include "3ad2ant1.mm"
include "fveq2d.mm"
include "co.mm"
include "df-ov.mm"
include "fzfi.mm"
include "eqeltrri.mm"
include "syl6eqel.mm"
include "difss.mm"
include "dmss.mm"
include "ax-mp.mm"
include "simp3.mm"
include "syl5ss.mm"
include "ssfi.mm"
include "syl2anc.mm"
include "fnfi.mm"
include "p0ex.mm"
include "unexg.mm"
include "sylancl.mm"
include "ssexg.mm"
include "sylancr.mm"
include "elex.mm"
include "jca.mm"
include "cv.mm"
include "simpr.mm"
include "eleq1d.mm"
include "simpl.mm"
include "difeq1d.mm"
include "funeqd.mm"
include "dmeqd.mm"
include "sseq12d.mm"
include "3anbi123d.mm"
include "df-struct.mm"
include "brabga.mm"
include "pm5.21nii.mm"

theorem isstruct2
  let cF: class F
  let cX: class X
  let vf: setvar f
  let vx: setvar x


  assert |- ( F Struct X <-> ( X e. ( <_ i^i ( NN X. NN ) ) /\ Fun ( F \ { (/) } ) /\ dom F C_ ( ... ` X ) ) )

  proof
    cF
    cX
    cstr
    wbr
    #
    cF
    cvv
    wcel
    #
    cX
    cvv
    wcel
    #
    wa
    #
    cX
    cle
    cn
    cn
    cxp
    #
    cin
    #
    wcel
    #
    cF
    c0
    csn
    #
    cdif
    #
    wfun
    #
    cF
    cdm
    #
    cX
    cfz
    cfv
    #
    wss
    #
    w3a
    #
    cstr
    wrel
    @0
    @3
    brstruct
    cF
    cX
    cstr
    brrelex12
    mpan
    @13
    @1
    @2
    @13
    cF
    @8
    @7
    cun
    #
    wss
    @14
    cvv
    wcel
    #
    @1
    cF
    cF
    @7
    cun
    @14
    cF
    @7
    ssun1
    cF
    @7
    undif1
    sseqtr4i
    @13
    @8
    cfn
    wcel
    #
    @7
    cvv
    wcel
    @15
    @13
    @8
    @8
    cdm
    #
    wfn
    #
    @17
    cfn
    wcel
    #
    @16
    @13
    @9
    @18
    @6
    @9
    @12
    simp2
    @8
    funfn
    sylib
    @13
    @11
    cfn
    wcel
    @17
    @11
    wss
    @19
    @13
    @11
    cX
    c1st
    cfv
    #
    cX
    c2nd
    cfv
    #
    cop
    #
    cfz
    cfv
    #
    cfn
    @13
    cX
    @22
    cfz
    @6
    @9
    cX
    @22
    wceq
    #
    @12
    @6
    cX
    @4
    wcel
    @24
    @5
    @4
    cX
    cle
    @4
    inss2
    sseli
    cX
    cn
    cn
    1st2nd2
    syl
    3ad2ant1
    fveq2d
    @20
    @21
    cfz
    co
    @23
    cfn
    @20
    @21
    cfz
    df-ov
    @20
    @21
    fzfi
    eqeltrri
    syl6eqel
    @13
    @17
    @10
    @11
    @8
    cF
    wss
    @17
    @10
    wss
    cF
    @7
    difss
    @8
    cF
    dmss
    ax-mp
    @6
    @9
    @12
    simp3
    syl5ss
    @11
    @17
    ssfi
    syl2anc
    @17
    @8
    fnfi
    syl2anc
    p0ex
    @8
    @7
    cfn
    cvv
    unexg
    sylancl
    cF
    @14
    cvv
    ssexg
    sylancr
    @6
    @9
    @2
    @12
    cX
    @5
    elex
    3ad2ant1
    jca
    vx
    cv
    #
    @5
    wcel
    #
    vf
    cv
    #
    @7
    cdif
    #
    wfun
    #
    @27
    cdm
    #
    @25
    cfz
    cfv
    #
    wss
    #
    w3a
    @13
    vf
    vx
    cF
    cX
    cstr
    cvv
    cvv
    @27
    cF
    wceq
    #
    @25
    cX
    wceq
    #
    wa
    #
    @26
    @6
    @29
    @9
    @32
    @12
    @35
    @25
    cX
    @5
    @33
    @34
    simpr
    #
    eleq1d
    @35
    @28
    @8
    @35
    @27
    cF
    @7
    @33
    @34
    simpl
    #
    difeq1d
    funeqd
    @35
    @30
    @10
    @31
    @11
    @35
    @27
    cF
    @37
    dmeqd
    @35
    @25
    cX
    cfz
    @36
    fveq2d
    sseq12d
    3anbi123d
    vx
    vf
    df-struct
    brabga
    pm5.21nii
end
