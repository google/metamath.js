include "cxr.mm"
include "clt.mm"
include "cinf.mm"
include "cc0.mm"
include "cpnf.mm"
include "cicc.mm"
include "co.mm"
include "iccssxr.mm"
include "sseldi.mm"
include "wcel.mm"
include "0xr.mm"
include "a1i.mm"
include "wss.mm"
include "cle.mm"
include "wbr.mm"
include "cv.mm"
include "cn.mm"
include "cico.mm"
include "cfv.mm"
include "ccom.mm"
include "cvol.mm"
include "cprod.mm"
include "cmpt.mm"
include "csumge0.mm"
include "wceq.mm"
include "cr.mm"
include "cxp.mm"
include "cmap.mm"
include "wrex.mm"
include "crab.mm"
include "ssrab2.mm"
include "eqsstri.mm"
include "wa.mm"
include "wf.mm"
include "c1.mm"
include "cop.mm"
include "1re.mm"
include "0re.mm"
include "pm3.2i.mm"
include "opelxp.mm"
include "mpbir.mm"
include "eqid.mm"
include "fmptd.mm"
include "cvv.mm"
include "cfn.mm"
include "wb.mm"
include "reex.mm"
include "xpex.mm"
include "elmapg.mm"
include "syl2anc.mm"
include "mpbird.mm"
include "adantr.mm"
include "ovexd.mm"
include "nnex.mm"
include "wex.mm"
include "c0.mm"
include "wne.mm"
include "n0.mm"
include "sylib.mm"
include "nfv.mm"
include "nfcv.mm"
include "ad2antrr.mm"
include "cc.mm"
include "c1st.mm"
include "c2nd.mm"
include "ffvelrnda.mm"
include "elmapi.mm"
include "syl.mm"
include "simpr.mm"
include "fvovco.mm"
include "elexd.mm"
include "fvmpt2.mm"
include "eqidd.mm"
include "elexi.mm"
include "fvmptd.mm"
include "fveq2d.mm"
include "op1st.mm"
include "eqtrd.mm"
include "op2nd.mm"
include "oveq12d.mm"
include "0le1.mm"
include "rexri.mm"
include "ico0.mm"
include "mp2an.mm"
include "3eqtrd.mm"
include "vol0.mm"
include "0cn.mm"
include "eqeltrd.mm"
include "adantlr.mm"
include "fveq2.mm"
include "wi.mm"
include "eleq1.mm"
include "anbi2d.mm"
include "eqeq1d.mm"
include "imbi12d.mm"
include "chvarv.mm"
include "fprod0.mm"
include "ex.mm"
include "exlimdv.mm"
include "mpd.mm"
include "mpteq2dva.mm"
include "sge0z.mm"
include "3eqtrrd.mm"
include "fveq1.mm"
include "coeq2d.mm"
include "fveq1d.mm"
include "ralrimivw.mm"
include "prodeq2d.mm"
include "mpteq2dv.mm"
include "eqeq2d.mm"
include "rspcev.mm"
include "jca.mm"
include "eqeq1.mm"
include "rexbidv.mm"
include "elrab2.mm"
include "sylibr.mm"
include "infxrlb.mm"
include "pnfxr.mm"
include "iccgelb.mm"
include "syl3anc.mm"
include "xrletrid.mm"

theorem ovn0lem
  let wph: wff ph
  let vz: setvar z
  let vi: setvar i
  let vj: setvar j
  let vk: setvar k
  let cI: class I
  let cM: class M
  let cX: class X
  let vl: setvar l
  let vx: setvar x
  assume ovn0lem.x: |- ( ph -> X e. Fin )
  assume ovn0lem.n0: |- ( ph -> X =/= (/) )
  assume ovn0lem.m: |- M = { z e. RR* | E. i e. ( ( ( RR X. RR ) ^m X ) ^m NN ) z = ( sum^ ` ( j e. NN |-> prod_ k e. X ( vol ` ( ( [,) o. ( i ` j ) ) ` k ) ) ) ) }
  assume ovn0lem.infm: |- ( ph -> inf ( M , RR* , < ) e. ( 0 [,] +oo ) )
  assume ovn0lem.i: |- I = ( j e. NN |-> ( l e. X |-> <. 1 , 0 >. ) )

  disjoint I i
  disjoint I j
  disjoint I k
  disjoint i j
  disjoint i k
  disjoint j k
  disjoint I l
  disjoint j l
  disjoint k l
  disjoint X i
  disjoint X j
  disjoint X k
  disjoint X z
  disjoint i z
  disjoint j z
  disjoint k z
  disjoint X l
  disjoint j ph
  disjoint k ph
  disjoint l ph
  disjoint k x
  assert |- ( ph -> inf ( M , RR* , < ) = 0 )

  proof
    wph
    cM
    cxr
    clt
    cinf
    #
    cc0
    wph
    cc0
    cpnf
    cicc
    co
    #
    cxr
    @0
    cc0
    cpnf
    iccssxr
    ovn0lem.infm
    sseldi
    cc0
    cxr
    wcel
    #
    wph
    0xr
    a1i
    #
    wph
    cM
    cxr
    wss
    #
    cc0
    cM
    wcel
    #
    @0
    cc0
    cle
    wbr
    @4
    wph
    cM
    vz
    cv
    #
    vj
    cn
    cX
    vk
    cv
    #
    cico
    vj
    cv
    #
    vi
    cv
    #
    cfv
    #
    ccom
    #
    cfv
    #
    cvol
    cfv
    #
    vk
    cprod
    #
    cmpt
    #
    csumge0
    cfv
    #
    wceq
    #
    vi
    cr
    cr
    cxp
    #
    cX
    cmap
    co
    #
    cn
    cmap
    co
    #
    wrex
    #
    vz
    cxr
    crab
    cxr
    ovn0lem.m
    @21
    vz
    cxr
    ssrab2
    eqsstri
    a1i
    wph
    @2
    cc0
    @16
    wceq
    #
    vi
    @20
    wrex
    #
    wa
    @5
    wph
    @2
    @23
    @3
    wph
    cI
    @20
    wcel
    #
    cc0
    vj
    cn
    cX
    @7
    cico
    @8
    cI
    cfv
    #
    ccom
    #
    cfv
    #
    cvol
    cfv
    #
    vk
    cprod
    #
    cmpt
    #
    csumge0
    cfv
    #
    wceq
    #
    @23
    wph
    @24
    cn
    @19
    cI
    wf
    #
    wph
    vj
    cn
    vl
    cX
    c1
    cc0
    cop
    #
    cmpt
    #
    @19
    cI
    wph
    @35
    @19
    wcel
    #
    @8
    cn
    wcel
    #
    wph
    @36
    cX
    @18
    @35
    wf
    #
    wph
    vl
    cX
    @34
    @18
    @35
    @34
    @18
    wcel
    #
    wph
    vl
    cv
    #
    cX
    wcel
    #
    wa
    @39
    c1
    cr
    wcel
    #
    cc0
    cr
    wcel
    #
    wa
    @42
    @43
    1re
    0re
    pm3.2i
    c1
    cc0
    cr
    cr
    opelxp
    mpbir
    #
    a1i
    @35
    eqid
    fmptd
    wph
    @18
    cvv
    wcel
    #
    cX
    cfn
    wcel
    #
    @36
    @38
    wb
    @45
    wph
    cr
    cr
    reex
    reex
    xpex
    a1i
    ovn0lem.x
    @18
    cX
    @35
    cvv
    cfn
    elmapg
    syl2anc
    mpbird
    adantr
    #
    ovn0lem.i
    fmptd
    #
    wph
    @19
    cvv
    wcel
    cn
    cvv
    wcel
    #
    @24
    @33
    wb
    wph
    @18
    cX
    cmap
    ovexd
    @49
    wph
    nnex
    a1i
    #
    @19
    cn
    cI
    cvv
    cvv
    elmapg
    syl2anc
    mpbird
    wph
    @31
    vj
    cn
    cc0
    cmpt
    #
    csumge0
    cfv
    cc0
    cc0
    wph
    @30
    @51
    csumge0
    wph
    vj
    cn
    @29
    cc0
    wph
    @37
    wa
    #
    @41
    vl
    wex
    #
    @29
    cc0
    wceq
    #
    wph
    @53
    @37
    wph
    cX
    c0
    wne
    @53
    ovn0lem.n0
    vl
    cX
    n0
    sylib
    adantr
    @52
    @41
    @54
    vl
    @52
    @41
    @54
    @52
    @41
    wa
    #
    cX
    @28
    @40
    @26
    cfv
    #
    cvol
    cfv
    #
    vk
    @40
    @55
    vk
    nfv
    vk
    @57
    nfcv
    wph
    @46
    @37
    @41
    ovn0lem.x
    ad2antrr
    @52
    @7
    cX
    wcel
    #
    @28
    cc
    wcel
    @41
    @52
    @58
    wa
    #
    @28
    cc0
    cc
    @59
    @28
    c0
    cvol
    cfv
    #
    cc0
    @59
    @27
    c0
    cvol
    @59
    @27
    @7
    @25
    cfv
    #
    c1st
    cfv
    #
    @61
    c2nd
    cfv
    #
    cico
    co
    c1
    cc0
    cico
    co
    #
    c0
    @59
    @25
    cico
    cr
    cr
    cX
    @7
    @52
    cX
    @18
    @25
    wf
    #
    @58
    @52
    @25
    @19
    wcel
    @65
    wph
    cn
    @19
    @8
    cI
    @48
    ffvelrnda
    @25
    @18
    cX
    elmapi
    syl
    adantr
    @52
    @58
    simpr
    #
    fvovco
    @59
    @62
    c1
    @63
    cc0
    cico
    @59
    @62
    @34
    c1st
    cfv
    #
    c1
    @59
    @61
    @34
    c1st
    @59
    vl
    @7
    @34
    @34
    cX
    @25
    cvv
    @52
    @25
    @35
    wceq
    #
    @58
    @52
    @37
    @35
    cvv
    wcel
    @68
    wph
    @37
    simpr
    @52
    @35
    @19
    @47
    elexd
    vj
    cn
    @35
    cvv
    cI
    ovn0lem.i
    fvmpt2
    syl2anc
    adantr
    @59
    @40
    @7
    wceq
    wa
    @34
    eqidd
    @66
    @34
    cvv
    wcel
    @59
    @34
    @18
    @44
    elexi
    a1i
    fvmptd
    #
    fveq2d
    @67
    c1
    wceq
    @59
    c1
    cc0
    c1
    cr
    1re
    elexi
    #
    cc0
    cxr
    0xr
    elexi
    #
    op1st
    a1i
    eqtrd
    @59
    @63
    @34
    c2nd
    cfv
    #
    cc0
    @59
    @61
    @34
    c2nd
    @69
    fveq2d
    @72
    cc0
    wceq
    @59
    c1
    cc0
    @70
    @71
    op2nd
    a1i
    eqtrd
    oveq12d
    @64
    c0
    wceq
    #
    @59
    @73
    cc0
    c1
    cle
    wbr
    #
    0le1
    c1
    cxr
    wcel
    @2
    @73
    @74
    wb
    c1
    1re
    rexri
    0xr
    c1
    cc0
    ico0
    mp2an
    mpbir
    a1i
    3eqtrd
    fveq2d
    @60
    cc0
    wceq
    @59
    vol0
    a1i
    eqtrd
    #
    cc0
    cc
    wcel
    @59
    0cn
    a1i
    eqeltrd
    adantlr
    @7
    @40
    wceq
    #
    @27
    @56
    cvol
    @7
    @40
    @26
    fveq2
    fveq2d
    #
    @52
    @41
    simpr
    @59
    @28
    cc0
    wceq
    #
    wi
    @55
    @57
    cc0
    wceq
    #
    wi
    vk
    vl
    @76
    @59
    @55
    @78
    @79
    @76
    @58
    @41
    @52
    @7
    @40
    cX
    eleq1
    anbi2d
    @76
    @28
    @57
    cc0
    @77
    eqeq1d
    imbi12d
    @75
    chvarv
    fprod0
    ex
    exlimdv
    mpd
    mpteq2dva
    fveq2d
    wph
    cn
    vj
    cvv
    wph
    vj
    nfv
    @50
    sge0z
    wph
    cc0
    eqidd
    3eqtrrd
    @22
    @32
    vi
    cI
    @20
    @9
    cI
    wceq
    #
    @16
    @31
    cc0
    @80
    @15
    @30
    csumge0
    @80
    vj
    cn
    @14
    @29
    @80
    cX
    @13
    @28
    vk
    @80
    @13
    @28
    wceq
    vk
    cX
    @80
    @12
    @27
    cvol
    @80
    @7
    @11
    @26
    @80
    @10
    @25
    cico
    @8
    @9
    cI
    fveq1
    coeq2d
    fveq1d
    fveq2d
    ralrimivw
    prodeq2d
    mpteq2dv
    fveq2d
    eqeq2d
    rspcev
    syl2anc
    jca
    @21
    @23
    vz
    cc0
    cxr
    cM
    @6
    cc0
    wceq
    @17
    @22
    vi
    @20
    @6
    cc0
    @16
    eqeq1
    rexbidv
    ovn0lem.m
    elrab2
    sylibr
    cM
    cc0
    infxrlb
    syl2anc
    wph
    @2
    cpnf
    cxr
    wcel
    #
    @0
    @1
    wcel
    cc0
    @0
    cle
    wbr
    @3
    @81
    wph
    pnfxr
    a1i
    ovn0lem.infm
    cc0
    cpnf
    @0
    iccgelb
    syl3anc
    xrletrid
end
