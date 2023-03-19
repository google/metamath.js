include "cres.mm"
include "cgsu.mm"
include "co.mm"
include "cc0.mm"
include "cxad.mm"
include "cdif.mm"
include "cle.mm"
include "cxr.mm"
include "wcel.mm"
include "wbr.mm"
include "cpw.mm"
include "cfn.mm"
include "cin.mm"
include "cv.mm"
include "cmpt.mm"
include "crn.mm"
include "wf.mm"
include "wss.mm"
include "wa.mm"
include "cpnf.mm"
include "cicc.mm"
include "iccssxr.mm"
include "cbs.mm"
include "cfv.mm"
include "wceq.mm"
include "cxrs.mm"
include "xrsbas.mm"
include "ressbas2.mm"
include "ax-mp.mm"
include "cmnf.mm"
include "csn.mm"
include "cress.mm"
include "csubmnd.mm"
include "c0g.mm"
include "eqid.mm"
include "xrge0subm.mm"
include "cvv.mm"
include "xrex.mm"
include "difexg.mm"
include "wne.mm"
include "simpl.mm"
include "ge0nemnf.mm"
include "jca.mm"
include "elxrge0.mm"
include "eldifsn.mm"
include "3imtr4i.mm"
include "ssriv.mm"
include "ressabs.mm"
include "mp2an.mm"
include "eqtr4i.mm"
include "xrs10.mm"
include "subm0.mm"
include "ccmn.mm"
include "xrge0cmn.mm"
include "eqeltri.mm"
include "a1i.mm"
include "elfpw.mm"
include "simprbi.mm"
include "adantl.mm"
include "simplbi.mm"
include "fssres.mm"
include "syl2an.mm"
include "c0ex.mm"
include "fdmfifsupp.mm"
include "gsumcl.mm"
include "sseldi.mm"
include "fmptd.mm"
include "frn.mm"
include "syl.mm"
include "c0.mm"
include "cc.mm"
include "0ss.mm"
include "0fin.mm"
include "mpbir2an.mm"
include "0cn.mm"
include "reseq2.mm"
include "res0.mm"
include "syl6eq.mm"
include "oveq2d.mm"
include "gsum0.mm"
include "elrnmpt1s.mm"
include "sseldd.mm"
include "diffi.mm"
include "ssdifssd.mm"
include "fssresd.mm"
include "ssfi.mm"
include "syl2anc.mm"
include "sstrd.mm"
include "xleadd2a.mm"
include "syl31anc.mm"
include "xaddid1.mm"
include "cplusg.mm"
include "ovex.mm"
include "xrsadd.mm"
include "ressplusg.mm"
include "disjdif.mm"
include "cun.mm"
include "undif2.mm"
include "ssequn1.mm"
include "sylib.mm"
include "syl5req.mm"
include "gsumsplit.mm"
include "resabs1d.mm"
include "difss.mm"
include "resabs1.mm"
include "mp1i.mm"
include "oveq12d.mm"
include "eqtr2d.mm"
include "3brtr3d.mm"

theorem xrge0gsumle
  let wph: wff ph
  let cA: class A
  let cB: class B
  let cC: class C
  let cF: class F
  let cG: class G
  let cV: class V
  let vs: setvar s
  let vx: setvar x
  assume xrge0gsumle.g: |- G = ( RR*s |`s ( 0 [,] +oo ) )
  assume xrge0gsumle.a: |- ( ph -> A e. V )
  assume xrge0gsumle.f: |- ( ph -> F : A --> ( 0 [,] +oo ) )
  assume xrge0gsumle.b: |- ( ph -> B e. ( ~P A i^i Fin ) )
  assume xrge0gsumle.c: |- ( ph -> C C_ B )


  assert |- ( ph -> ( G gsum ( F |` C ) ) <_ ( G gsum ( F |` B ) ) )

  proof
    wph
    cG
    cF
    cC
    cres
    #
    cgsu
    co
    #
    cc0
    cxad
    co
    #
    @1
    cG
    cF
    cB
    cC
    cdif
    #
    cres
    #
    cgsu
    co
    #
    cxad
    co
    #
    @1
    cG
    cF
    cB
    cres
    #
    cgsu
    co
    #
    cle
    wph
    cc0
    cxr
    wcel
    @5
    cxr
    wcel
    #
    @1
    cxr
    wcel
    #
    cc0
    @5
    cle
    wbr
    #
    @2
    @6
    cle
    wbr
    wph
    vs
    cA
    cpw
    cfn
    cin
    #
    cG
    cF
    vs
    cv
    #
    cres
    #
    cgsu
    co
    #
    cmpt
    #
    crn
    #
    cxr
    cc0
    wph
    @12
    cxr
    @16
    wf
    @17
    cxr
    wss
    wph
    vs
    @12
    @15
    cxr
    @16
    wph
    @13
    @12
    wcel
    #
    wa
    #
    cc0
    cpnf
    cicc
    co
    #
    cxr
    @15
    cc0
    cpnf
    iccssxr
    #
    @19
    @13
    @20
    @14
    cG
    cfn
    cc0
    @20
    cxr
    wss
    @20
    cG
    cbs
    cfv
    wceq
    @21
    @20
    cxr
    cG
    cxrs
    xrge0gsumle.g
    xrsbas
    ressbas2
    ax-mp
    #
    @20
    cxrs
    cxr
    cmnf
    csn
    #
    cdif
    #
    cress
    co
    #
    csubmnd
    cfv
    wcel
    cc0
    cG
    c0g
    cfv
    wceq
    @25
    @25
    eqid
    #
    xrge0subm
    @20
    cG
    @25
    cc0
    cG
    cxrs
    @20
    cress
    co
    #
    @25
    @20
    cress
    co
    #
    xrge0gsumle.g
    @24
    cvv
    wcel
    #
    @20
    @24
    wss
    @28
    @27
    wceq
    cxr
    cvv
    wcel
    @29
    xrex
    cxr
    @23
    cvv
    difexg
    ax-mp
    vx
    @20
    @24
    vx
    cv
    #
    cxr
    wcel
    #
    cc0
    @30
    cle
    wbr
    #
    wa
    #
    @31
    @30
    cmnf
    wne
    #
    wa
    @30
    @20
    wcel
    @30
    @24
    wcel
    @33
    @31
    @34
    @31
    @32
    simpl
    @30
    ge0nemnf
    jca
    @30
    elxrge0
    @30
    cxr
    cmnf
    eldifsn
    3imtr4i
    ssriv
    @24
    @20
    cxrs
    cvv
    ressabs
    mp2an
    eqtr4i
    @25
    @26
    xrs10
    subm0
    ax-mp
    #
    cG
    ccmn
    wcel
    #
    @19
    cG
    @27
    ccmn
    xrge0gsumle.g
    xrge0cmn
    eqeltri
    #
    a1i
    @18
    @13
    cfn
    wcel
    #
    wph
    @18
    @13
    cA
    wss
    #
    @38
    @13
    cA
    elfpw
    #
    simprbi
    adantl
    #
    wph
    cA
    @20
    cF
    wf
    @39
    @13
    @20
    @14
    wf
    @18
    xrge0gsumle.f
    @18
    @39
    @38
    @40
    simplbi
    cA
    @20
    @13
    cF
    fssres
    syl2an
    #
    @19
    @13
    @20
    @14
    cvv
    cc0
    @42
    @41
    cc0
    cvv
    wcel
    #
    @19
    c0ex
    a1i
    fdmfifsupp
    gsumcl
    sseldi
    @16
    eqid
    #
    fmptd
    @12
    cxr
    @16
    frn
    syl
    cc0
    @17
    wcel
    #
    wph
    c0
    @12
    wcel
    #
    cc0
    cc
    wcel
    @45
    @46
    c0
    cA
    wss
    c0
    cfn
    wcel
    cA
    0ss
    0fin
    c0
    cA
    elfpw
    mpbir2an
    0cn
    vs
    @12
    @15
    cc0
    c0
    @16
    cc
    @44
    @13
    c0
    wceq
    #
    @15
    cG
    c0
    cgsu
    co
    cc0
    @47
    @14
    c0
    cG
    cgsu
    @47
    @14
    cF
    c0
    cres
    c0
    @13
    c0
    cF
    reseq2
    cF
    res0
    syl6eq
    oveq2d
    cG
    cc0
    @35
    gsum0
    syl6eq
    elrnmpt1s
    mp2an
    a1i
    sseldd
    wph
    @20
    cxr
    @5
    @21
    wph
    @3
    @20
    @4
    cG
    cfn
    cc0
    @22
    @35
    @36
    wph
    @37
    a1i
    #
    wph
    cB
    cfn
    wcel
    #
    @3
    cfn
    wcel
    wph
    cB
    @12
    wcel
    #
    @49
    xrge0gsumle.b
    @50
    cB
    cA
    wss
    #
    @49
    cB
    cA
    elfpw
    #
    simprbi
    syl
    #
    cB
    cC
    diffi
    syl
    #
    wph
    cA
    @20
    @3
    cF
    xrge0gsumle.f
    wph
    cB
    cA
    cC
    wph
    @50
    @51
    xrge0gsumle.b
    @50
    @51
    @49
    @52
    simplbi
    syl
    #
    ssdifssd
    fssresd
    #
    wph
    @3
    @20
    @4
    cvv
    cc0
    @56
    @54
    @43
    wph
    c0ex
    a1i
    #
    fdmfifsupp
    gsumcl
    #
    sseldi
    wph
    @20
    cxr
    @1
    @21
    wph
    cC
    @20
    @0
    cG
    cfn
    cc0
    @22
    @35
    @48
    wph
    @49
    cC
    cB
    wss
    #
    cC
    cfn
    wcel
    @53
    xrge0gsumle.c
    cB
    cC
    ssfi
    syl2anc
    #
    wph
    cA
    @20
    cC
    cF
    xrge0gsumle.f
    wph
    cC
    cB
    cA
    xrge0gsumle.c
    @55
    sstrd
    fssresd
    #
    wph
    cC
    @20
    @0
    cvv
    cc0
    @61
    @60
    @57
    fdmfifsupp
    gsumcl
    sseldi
    #
    wph
    @5
    @20
    wcel
    #
    @11
    @58
    @63
    @9
    @11
    @5
    elxrge0
    simprbi
    syl
    cc0
    @5
    @1
    xleadd2a
    syl31anc
    wph
    @10
    @2
    @1
    wceq
    @62
    @1
    xaddid1
    syl
    wph
    @8
    cG
    @7
    cC
    cres
    #
    cgsu
    co
    #
    cG
    @7
    @3
    cres
    #
    cgsu
    co
    #
    cxad
    co
    @6
    wph
    cB
    @20
    cC
    @3
    cxad
    @7
    cG
    @12
    cc0
    @22
    @35
    @20
    cvv
    wcel
    cxad
    cG
    cplusg
    cfv
    wceq
    cc0
    cpnf
    cicc
    ovex
    @20
    cxad
    cxrs
    cG
    cvv
    xrge0gsumle.g
    xrsadd
    ressplusg
    ax-mp
    @48
    xrge0gsumle.b
    wph
    cA
    @20
    cB
    cF
    xrge0gsumle.f
    @55
    fssresd
    #
    wph
    cB
    @20
    @7
    cvv
    cc0
    @68
    @53
    @57
    fdmfifsupp
    cC
    @3
    cin
    c0
    wceq
    wph
    cC
    cB
    disjdif
    a1i
    wph
    cC
    @3
    cun
    cC
    cB
    cun
    #
    cB
    cC
    cB
    undif2
    wph
    @59
    @69
    cB
    wceq
    xrge0gsumle.c
    cC
    cB
    ssequn1
    sylib
    syl5req
    gsumsplit
    wph
    @65
    @1
    @67
    @5
    cxad
    wph
    @64
    @0
    cG
    cgsu
    wph
    cF
    cC
    cB
    xrge0gsumle.c
    resabs1d
    oveq2d
    wph
    @66
    @4
    cG
    cgsu
    @3
    cB
    wss
    @66
    @4
    wceq
    wph
    cB
    cC
    difss
    cF
    @3
    cB
    resabs1
    mp1i
    oveq2d
    oveq12d
    eqtr2d
    3brtr3d
end
