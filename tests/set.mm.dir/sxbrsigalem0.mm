include "cr.mm"
include "cv.mm"
include "cpnf.mm"
include "cico.mm"
include "co.mm"
include "cxp.mm"
include "cmpt.mm"
include "crn.mm"
include "cun.mm"
include "cuni.mm"
include "wss.mm"
include "unissb.mm"
include "wcel.mm"
include "wo.mm"
include "elun.mm"
include "cpw.mm"
include "eqid.mm"
include "rnmptss.mm"
include "cxr.mm"
include "pnfxr.mm"
include "icossre.mm"
include "mpan2.mm"
include "xpss1.mm"
include "syl.mm"
include "ovex.mm"
include "reex.mm"
include "xpex.mm"
include "elpw.mm"
include "sylibr.mm"
include "mprg.mm"
include "sseli.mm"
include "elpwid.mm"
include "xpss2.mm"
include "jaoi.mm"
include "sylbi.mm"
include "mprgbir.mm"
include "wfun.mm"
include "c1st.mm"
include "cfv.mm"
include "funmpt.mm"
include "cvv.mm"
include "c2nd.mm"
include "wa.mm"
include "clt.mm"
include "wbr.mm"
include "rexr.mm"
include "a1i.mm"
include "ltpnf.mm"
include "lbico1.mm"
include "syl3anc.mm"
include "anim1i.mm"
include "anim2i.mm"
include "elxp7.mm"
include "3imtr4i.mm"
include "wceq.mm"
include "xp1st.mm"
include "oveq1.mm"
include "xpeq1d.mm"
include "fvmpt.mm"
include "eleqtrrd.mm"
include "elunirn2.mm"
include "sylancr.mm"
include "ssriv.mm"
include "ssun3.mm"
include "ax-mp.mm"
include "uniun.mm"
include "sseqtr4i.mm"
include "eqssi.mm"

theorem sxbrsigalem0
  let ve: setvar e
  let vf: setvar f
  let vz: setvar z

  disjoint e f
  disjoint e z
  disjoint f z
  assert |- U. ( ran ( e e. RR |-> ( ( e [,) +oo ) X. RR ) ) u. ran ( f e. RR |-> ( RR X. ( f [,) +oo ) ) ) ) = ( RR X. RR )

  proof
    ve
    cr
    ve
    cv
    #
    cpnf
    cico
    co
    #
    cr
    cxp
    #
    cmpt
    #
    crn
    #
    vf
    cr
    cr
    vf
    cv
    #
    cpnf
    cico
    co
    #
    cxp
    #
    cmpt
    #
    crn
    #
    cun
    #
    cuni
    #
    cr
    cr
    cxp
    #
    @11
    @12
    wss
    vz
    cv
    #
    @12
    wss
    #
    vz
    @10
    vz
    @10
    @12
    unissb
    @13
    @10
    wcel
    @13
    @4
    wcel
    #
    @13
    @9
    wcel
    #
    wo
    @14
    @13
    @4
    @9
    elun
    @15
    @14
    @16
    @15
    @13
    @12
    @4
    @12
    cpw
    #
    @13
    @2
    @17
    wcel
    #
    @4
    @17
    wss
    ve
    cr
    ve
    cr
    @2
    @17
    @3
    @3
    eqid
    #
    rnmptss
    @0
    cr
    wcel
    #
    @2
    @12
    wss
    #
    @18
    @20
    @1
    cr
    wss
    #
    @21
    @20
    cpnf
    cxr
    wcel
    #
    @22
    pnfxr
    @0
    cpnf
    icossre
    mpan2
    @1
    cr
    cr
    xpss1
    syl
    @2
    @12
    @1
    cr
    @0
    cpnf
    cico
    ovex
    reex
    xpex
    elpw
    sylibr
    mprg
    sseli
    elpwid
    @16
    @13
    @12
    @9
    @17
    @13
    @7
    @17
    wcel
    #
    @9
    @17
    wss
    vf
    cr
    vf
    cr
    @7
    @17
    @8
    @8
    eqid
    rnmptss
    @5
    cr
    wcel
    #
    @7
    @12
    wss
    #
    @24
    @25
    @6
    cr
    wss
    #
    @26
    @25
    @23
    @27
    pnfxr
    @5
    cpnf
    icossre
    mpan2
    @6
    cr
    cr
    xpss2
    syl
    @7
    @12
    cr
    @6
    reex
    @5
    cpnf
    cico
    ovex
    xpex
    elpw
    sylibr
    mprg
    sseli
    elpwid
    jaoi
    sylbi
    mprgbir
    @12
    @4
    cuni
    #
    @9
    cuni
    #
    cun
    #
    @11
    @12
    @28
    wss
    @12
    @30
    wss
    vz
    @12
    @28
    @13
    @12
    wcel
    #
    @3
    wfun
    @13
    @13
    c1st
    cfv
    #
    @3
    cfv
    #
    wcel
    @13
    @28
    wcel
    ve
    cr
    @2
    funmpt
    @31
    @13
    @32
    cpnf
    cico
    co
    #
    cr
    cxp
    #
    @33
    @13
    cvv
    cvv
    cxp
    wcel
    #
    @32
    cr
    wcel
    #
    @13
    c2nd
    cfv
    cr
    wcel
    #
    wa
    #
    wa
    @36
    @32
    @34
    wcel
    #
    @38
    wa
    #
    wa
    @31
    @13
    @35
    wcel
    @39
    @41
    @36
    @37
    @40
    @38
    @37
    @32
    cxr
    wcel
    @23
    @32
    cpnf
    clt
    wbr
    @40
    @32
    rexr
    @23
    @37
    pnfxr
    a1i
    @32
    ltpnf
    @32
    cpnf
    lbico1
    syl3anc
    anim1i
    anim2i
    @13
    cr
    cr
    elxp7
    @13
    @34
    cr
    elxp7
    3imtr4i
    @31
    @37
    @33
    @35
    wceq
    @13
    cr
    cr
    xp1st
    ve
    @32
    @2
    @35
    cr
    @3
    @0
    @32
    wceq
    @1
    @34
    cr
    @0
    @32
    cpnf
    cico
    oveq1
    xpeq1d
    @19
    @34
    cr
    @32
    cpnf
    cico
    ovex
    reex
    xpex
    fvmpt
    syl
    eleqtrrd
    @32
    @13
    @3
    elunirn2
    sylancr
    ssriv
    @12
    @28
    @29
    ssun3
    ax-mp
    @4
    @9
    uniun
    sseqtr4i
    eqssi
end
