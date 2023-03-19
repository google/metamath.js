include "cv.mm"
include "cesum.mm"
include "csn.mm"
include "cxp.mm"
include "ciun.mm"
include "wceq.mm"
include "c0.mm"
include "cun.mm"
include "esumeq1.mm"
include "nfv.mm"
include "iuneq1.mm"
include "esumeq1d.mm"
include "eqeq12d.mm"
include "cc0.mm"
include "esumnul.mm"
include "0iun.mm"
include "ax-mp.mm"
include "3eqtr4ri.mm"
include "a1i.mm"
include "wss.mm"
include "cdif.mm"
include "wcel.mm"
include "wa.mm"
include "cxad.mm"
include "co.mm"
include "csb.mm"
include "simpr.mm"
include "nfcsb1v.mm"
include "nfesum2.mm"
include "csbeq1a.mm"
include "esumeq12d.mm"
include "adantl.mm"
include "simprr.mm"
include "cpnf.mm"
include "cicc.mm"
include "wral.mm"
include "eldifad.mm"
include "adantlr.mm"
include "ralrimiva.mm"
include "rspcsbela.mm"
include "syl2anc.mm"
include "simpll.mm"
include "adantr.mm"
include "wsbc.mm"
include "ex.mm"
include "sbcimdv.mm"
include "sbcan.mm"
include "sbcel1v.mm"
include "sbcel2.mm"
include "anbi12i.mm"
include "bitri.mm"
include "cvv.mm"
include "wb.mm"
include "vex.mm"
include "sbcel1g.mm"
include "3imtr3g.mm"
include "imp.mm"
include "syl12anc.mm"
include "nfcv.mm"
include "esumcl.mm"
include "esumsnf.mm"
include "cop.mm"
include "wrex.mm"
include "cab.mm"
include "wi.mm"
include "nfeq2.mm"
include "nfim.mm"
include "opeq1.mm"
include "eqeq2d.mm"
include "imbi12d.mm"
include "chvar.mm"
include "cmpt.mm"
include "ccnv.mm"
include "wfun.mm"
include "vsnid.mm"
include "opelxpd.mm"
include "c2nd.mm"
include "cfv.mm"
include "wreu.mm"
include "xp2nd.mm"
include "c1st.mm"
include "xp1st.mm"
include "fvex.mm"
include "elsn.mm"
include "sylib.mm"
include "eqop.mm"
include "mpbirand.mm"
include "eqcom.mm"
include "syl6bb.mm"
include "ad2antlr.mm"
include "reu6i.mm"
include "syl2an2.mm"
include "f1mptrn.mm"
include "sbcfung.mm"
include "csbcnv.mm"
include "csbmpt12.mm"
include "csbopg.mm"
include "csbvarg.mm"
include "csbconstg.mm"
include "opeq12d.mm"
include "eqtrd.mm"
include "mpteq2dv.mm"
include "cnveqd.mm"
include "syl5eqr.mm"
include "funeqd.mm"
include "bitrd.mm"
include "syldan.mm"
include "esumc.mm"
include "nfab1.mm"
include "rexbidv.mm"
include "rexsn.mm"
include "elxp2.mm"
include "abid.mm"
include "3bitr4ri.mm"
include "eqri.mm"
include "syl6eq.mm"
include "oveq12d.mm"
include "snex.mm"
include "wn.mm"
include "cin.mm"
include "eldifbd.mm"
include "disjsn.mm"
include "sylibr.mm"
include "simprl.mm"
include "sselda.mm"
include "anassrs.mm"
include "snssd.mm"
include "esumsplit.mm"
include "iunxun.mm"
include "nfxp.mm"
include "sneq.mm"
include "xpeq12d.mm"
include "iunxsngf.mm"
include "uneq2i.mm"
include "eqtri.mm"
include "xpexg.mm"
include "sylancr.mm"
include "iunexg.mm"
include "wne.mm"
include "nelne2.mm"
include "disjsn2.mm"
include "xpdisj1.mm"
include "3syl.mm"
include "iuneq2dv.mm"
include "iunin1f.mm"
include "iun0.mm"
include "3eqtr3g.mm"
include "iunss1.mm"
include "syl.mm"
include "nfiu1.mm"
include "nfcri.mm"
include "nfan.mm"
include "nfel.mm"
include "simp-5l.mm"
include "simp-4r.mm"
include "simplr.mm"
include "eqeltrd.mm"
include "elsnxp.mm"
include "biimpa.mm"
include "adantll.mm"
include "r19.29af2.mm"
include "eliun.mm"
include "r19.29af.mm"
include "ssiun2sf.mm"
include "syl5eq.mm"
include "3eqtr4d.mm"
include "findcard2d.mm"

theorem esum2dlem
  let wph: wff ph
  let vz: setvar z
  let cA: class A
  let cB: class B
  let cC: class C
  let vj: setvar j
  let vk: setvar k
  let cF: class F
  let cV: class V
  let cW: class W
  let vi: setvar i
  let vl: setvar l
  let vt: setvar t
  let va: setvar a
  let vb: setvar b
  let vc: setvar c
  let vr: setvar r
  let vs: setvar s
  let vu: setvar u
  assume esum2d.0: |- F/_ k F
  assume esum2d.1: |- ( z = <. j , k >. -> F = C )
  assume esum2d.2: |- ( ph -> A e. V )
  assume esum2d.3: |- ( ( ph /\ j e. A ) -> B e. W )
  assume esum2d.4: |- ( ( ph /\ ( j e. A /\ k e. B ) ) -> C e. ( 0 [,] +oo ) )
  assume esum2dlem.e: |- ( ph -> A e. Fin )

  disjoint j k
  disjoint A j
  disjoint A k
  disjoint A z
  disjoint j z
  disjoint k z
  disjoint C z
  disjoint B k
  disjoint B z
  disjoint F j
  disjoint W j
  disjoint W k
  disjoint j ph
  disjoint k ph
  disjoint ph z
  disjoint i j
  disjoint i k
  disjoint i l
  disjoint i t
  disjoint j l
  disjoint j t
  disjoint k l
  disjoint k t
  disjoint l t
  disjoint A a
  disjoint A b
  disjoint A c
  disjoint A l
  disjoint A r
  disjoint A s
  disjoint A t
  disjoint A u
  disjoint a b
  disjoint a c
  disjoint a j
  disjoint a k
  disjoint a l
  disjoint a r
  disjoint a s
  disjoint a t
  disjoint a u
  disjoint a z
  disjoint b c
  disjoint b j
  disjoint b k
  disjoint b l
  disjoint b r
  disjoint b s
  disjoint b t
  disjoint b u
  disjoint b z
  disjoint c j
  disjoint c k
  disjoint c l
  disjoint c r
  disjoint c s
  disjoint c t
  disjoint c u
  disjoint c z
  disjoint j r
  disjoint j s
  disjoint j u
  disjoint k r
  disjoint k s
  disjoint k u
  disjoint l r
  disjoint l s
  disjoint l u
  disjoint l z
  disjoint r s
  disjoint r t
  disjoint r u
  disjoint r z
  disjoint s t
  disjoint s u
  disjoint s z
  disjoint t u
  disjoint t z
  disjoint u z
  disjoint C a
  disjoint C b
  disjoint C c
  disjoint C l
  disjoint C s
  disjoint C t
  disjoint C u
  disjoint B a
  disjoint B b
  disjoint B c
  disjoint B i
  disjoint B l
  disjoint B r
  disjoint B s
  disjoint B t
  disjoint B u
  disjoint a i
  disjoint b i
  disjoint c i
  disjoint i r
  disjoint i s
  disjoint i u
  disjoint i z
  disjoint F a
  disjoint F b
  disjoint F c
  disjoint F l
  disjoint F r
  disjoint F s
  disjoint F t
  disjoint F u
  disjoint a ph
  disjoint b ph
  disjoint c ph
  disjoint l ph
  disjoint ph r
  disjoint ph s
  disjoint ph t
  disjoint ph u
  assert |- ( ph -> sum* j e. A sum* k e. B C = sum* z e. U_ j e. A ( { j } X. B ) F )

  proof
    wph
    va
    cv
    #
    cB
    cC
    vk
    cesum
    #
    vj
    cesum
    #
    vj
    @0
    vj
    cv
    #
    csn
    #
    cB
    cxp
    #
    ciun
    #
    cF
    vz
    cesum
    #
    wceq
    c0
    @1
    vj
    cesum
    #
    vj
    c0
    @5
    ciun
    #
    cF
    vz
    cesum
    #
    wceq
    #
    vb
    cv
    #
    @1
    vj
    cesum
    #
    vj
    @12
    @5
    ciun
    #
    cF
    vz
    cesum
    #
    wceq
    #
    @12
    vl
    cv
    #
    csn
    #
    cun
    #
    @1
    vj
    cesum
    #
    vj
    @19
    @5
    ciun
    #
    cF
    vz
    cesum
    #
    wceq
    #
    cA
    @1
    vj
    cesum
    #
    vj
    cA
    @5
    ciun
    #
    cF
    vz
    cesum
    #
    wceq
    va
    vb
    vl
    cA
    @0
    c0
    wceq
    #
    @2
    @8
    @7
    @10
    @0
    c0
    @1
    vj
    esumeq1
    @27
    @6
    @9
    cF
    vz
    @27
    vz
    nfv
    vj
    @0
    c0
    @5
    iuneq1
    esumeq1d
    eqeq12d
    @0
    @12
    wceq
    #
    @2
    @13
    @7
    @15
    @0
    @12
    @1
    vj
    esumeq1
    @28
    @6
    @14
    cF
    vz
    @28
    vz
    nfv
    vj
    @0
    @12
    @5
    iuneq1
    esumeq1d
    eqeq12d
    @0
    @19
    wceq
    #
    @2
    @20
    @7
    @22
    @0
    @19
    @1
    vj
    esumeq1
    @29
    @6
    @21
    cF
    vz
    @29
    vz
    nfv
    vj
    @0
    @19
    @5
    iuneq1
    esumeq1d
    eqeq12d
    @0
    cA
    wceq
    #
    @2
    @24
    @7
    @26
    @0
    cA
    @1
    vj
    esumeq1
    @30
    @6
    @25
    cF
    vz
    @30
    vz
    nfv
    vj
    @0
    cA
    @5
    iuneq1
    esumeq1d
    eqeq12d
    @11
    wph
    c0
    cF
    vz
    cesum
    #
    cc0
    @10
    @8
    vz
    cF
    esumnul
    @9
    c0
    wceq
    @10
    @31
    wceq
    vj
    @5
    0iun
    @9
    c0
    cF
    vz
    esumeq1
    ax-mp
    vj
    @1
    esumnul
    3eqtr4ri
    a1i
    wph
    @12
    cA
    wss
    #
    @17
    cA
    @12
    cdif
    #
    wcel
    #
    wa
    #
    wa
    #
    @16
    @23
    @36
    @16
    wa
    #
    @13
    @18
    @1
    vj
    cesum
    #
    cxad
    co
    #
    @15
    @18
    vj
    @17
    cB
    csb
    #
    cxp
    #
    cF
    vz
    cesum
    #
    cxad
    co
    #
    @20
    @22
    @37
    @13
    @15
    @38
    @42
    cxad
    @36
    @16
    simpr
    @36
    @38
    @42
    wceq
    @16
    @36
    @38
    @40
    vj
    @17
    cC
    csb
    #
    vk
    cesum
    #
    @42
    @36
    @1
    @45
    vj
    @17
    @33
    vj
    @40
    @44
    vk
    vj
    @17
    cB
    nfcsb1v
    #
    vj
    @17
    cC
    nfcsb1v
    #
    nfesum2
    @3
    @17
    wceq
    #
    @1
    @45
    wceq
    @36
    @48
    cB
    @40
    cC
    @44
    vk
    vj
    @17
    cB
    csbeq1a
    #
    vj
    @17
    cC
    csbeq1a
    #
    esumeq12d
    adantl
    wph
    @32
    @34
    simprr
    #
    @36
    @40
    cW
    wcel
    #
    @44
    cc0
    cpnf
    cicc
    co
    #
    wcel
    #
    vk
    @40
    wral
    @45
    @53
    wcel
    @36
    @17
    cA
    wcel
    #
    cB
    cW
    wcel
    #
    vj
    cA
    wral
    @52
    @36
    @17
    cA
    @12
    @51
    eldifad
    #
    @36
    @56
    vj
    cA
    wph
    @3
    cA
    wcel
    #
    @56
    @35
    esum2d.3
    adantlr
    #
    ralrimiva
    vj
    @17
    cA
    cB
    cW
    rspcsbela
    syl2anc
    #
    @36
    @54
    vk
    @40
    @36
    vk
    cv
    #
    @40
    wcel
    #
    wa
    #
    wph
    @55
    @62
    @54
    wph
    @35
    @62
    simpll
    @36
    @55
    @62
    @57
    adantr
    @36
    @62
    simpr
    #
    wph
    @55
    @62
    wa
    #
    @54
    wph
    @58
    @61
    cB
    wcel
    #
    wa
    #
    vj
    @17
    wsbc
    #
    cC
    @53
    wcel
    #
    vj
    @17
    wsbc
    #
    @65
    @54
    wph
    @67
    @69
    vj
    @17
    wph
    @67
    @69
    esum2d.4
    ex
    sbcimdv
    @68
    @58
    vj
    @17
    wsbc
    #
    @66
    vj
    @17
    wsbc
    #
    wa
    @65
    @58
    @66
    vj
    @17
    sbcan
    @71
    @55
    @72
    @62
    vj
    @17
    cA
    sbcel1v
    #
    vj
    @17
    @61
    cB
    sbcel2
    anbi12i
    bitri
    @17
    cvv
    wcel
    #
    @70
    @54
    wb
    vl
    vex
    #
    vj
    @17
    cC
    @53
    cvv
    sbcel1g
    ax-mp
    3imtr3g
    imp
    syl12anc
    #
    ralrimiva
    @40
    @44
    vk
    cW
    vk
    @40
    nfcv
    #
    esumcl
    syl2anc
    esumsnf
    @36
    @45
    vt
    cv
    #
    @17
    @61
    cop
    #
    wceq
    #
    vk
    @40
    wrex
    #
    vt
    cab
    #
    cF
    vz
    cesum
    #
    @42
    @36
    vz
    vt
    @40
    @44
    @79
    cF
    vk
    cW
    @41
    esum2d.0
    @36
    vk
    nfv
    @77
    vz
    cv
    #
    @3
    @61
    cop
    #
    wceq
    #
    cF
    cC
    wceq
    #
    wi
    @84
    @79
    wceq
    #
    cF
    @44
    wceq
    #
    wi
    vj
    vl
    @88
    @89
    vj
    @88
    vj
    nfv
    vj
    cF
    @44
    @47
    nfeq2
    nfim
    @48
    @86
    @88
    @87
    @89
    @48
    @85
    @79
    @84
    @3
    @17
    @61
    opeq1
    eqeq2d
    @48
    cC
    @44
    cF
    @50
    eqeq2d
    imbi12d
    esum2d.1
    chvar
    @60
    wph
    @35
    @55
    vk
    @40
    @79
    cmpt
    #
    ccnv
    #
    wfun
    #
    @57
    wph
    @55
    @92
    wph
    @71
    vk
    cB
    @85
    cmpt
    #
    ccnv
    #
    wfun
    #
    vj
    @17
    wsbc
    #
    @55
    @92
    wph
    @58
    @95
    vj
    @17
    wph
    @58
    @95
    wph
    @58
    wa
    #
    vk
    vz
    cB
    @85
    @5
    @97
    @66
    wa
    #
    @3
    @61
    @4
    cB
    @3
    @4
    wcel
    @98
    vj
    vsnid
    a1i
    @97
    @66
    simpr
    opelxpd
    @84
    @5
    wcel
    #
    @84
    c2nd
    cfv
    #
    cB
    wcel
    @97
    @86
    @61
    @100
    wceq
    #
    wb
    #
    vk
    cB
    wral
    @86
    vk
    cB
    wreu
    @84
    @4
    cB
    xp2nd
    @97
    @99
    wa
    @102
    vk
    cB
    @99
    @102
    @97
    @66
    @99
    @86
    @100
    @61
    wceq
    #
    @101
    @99
    @86
    @84
    c1st
    cfv
    #
    @3
    wceq
    #
    @103
    @99
    @104
    @4
    wcel
    @105
    @84
    @4
    cB
    xp1st
    @104
    @3
    @84
    c1st
    fvex
    elsn
    sylib
    @84
    @3
    @61
    @4
    cB
    eqop
    mpbirand
    @100
    @61
    eqcom
    syl6bb
    ad2antlr
    ralrimiva
    @86
    vk
    cB
    @100
    reu6i
    syl2an2
    f1mptrn
    ex
    sbcimdv
    @73
    @74
    @96
    @92
    wb
    @75
    @74
    @96
    vj
    @17
    @94
    csb
    #
    wfun
    @92
    vj
    @17
    @94
    cvv
    sbcfung
    @74
    @106
    @91
    @74
    @106
    vj
    @17
    @93
    csb
    #
    ccnv
    @91
    vj
    @17
    @93
    csbcnv
    @74
    @107
    @90
    @74
    @107
    vk
    @40
    vj
    @17
    @85
    csb
    #
    cmpt
    @90
    vj
    vk
    @17
    cvv
    cB
    @85
    csbmpt12
    @74
    vk
    @40
    @108
    @79
    @74
    @108
    vj
    @17
    @3
    csb
    #
    vj
    @17
    @61
    csb
    #
    cop
    @79
    vj
    @17
    @3
    @61
    cvv
    csbopg
    @74
    @109
    @17
    @110
    @61
    vj
    @17
    cvv
    csbvarg
    vj
    @17
    @61
    cvv
    csbconstg
    opeq12d
    eqtrd
    mpteq2dv
    eqtrd
    cnveqd
    syl5eqr
    funeqd
    bitrd
    ax-mp
    3imtr3g
    imp
    syldan
    @76
    @63
    @17
    @61
    @18
    @40
    @17
    @18
    wcel
    @63
    vl
    vsnid
    a1i
    @64
    opelxpd
    esumc
    @82
    @41
    wceq
    @83
    @42
    wceq
    vt
    @82
    @41
    @81
    vt
    nfab1
    vt
    @41
    nfcv
    @78
    vi
    cv
    #
    @61
    cop
    #
    wceq
    #
    vk
    @40
    wrex
    #
    vi
    @18
    wrex
    @81
    @78
    @41
    wcel
    @78
    @82
    wcel
    @114
    @81
    vi
    @17
    @75
    @111
    @17
    wceq
    #
    @113
    @80
    vk
    @40
    @115
    @112
    @79
    @78
    @111
    @17
    @61
    opeq1
    eqeq2d
    rexbidv
    rexsn
    vi
    vk
    @78
    @18
    @40
    elxp2
    @81
    vt
    abid
    3bitr4ri
    eqri
    @82
    @41
    cF
    vz
    esumeq1
    ax-mp
    syl6eq
    eqtrd
    adantr
    oveq12d
    @36
    @20
    @39
    wceq
    @16
    @36
    @12
    @18
    @1
    vj
    @36
    vj
    nfv
    vj
    @12
    nfcv
    vj
    @18
    nfcv
    #
    @12
    cvv
    wcel
    #
    @36
    vb
    vex
    #
    a1i
    @18
    cvv
    wcel
    #
    @36
    @17
    snex
    #
    a1i
    @36
    @17
    @12
    wcel
    wn
    #
    @12
    @18
    cin
    c0
    wceq
    @36
    @17
    cA
    @12
    @51
    eldifbd
    #
    @12
    @17
    disjsn
    sylibr
    @36
    @3
    @12
    wcel
    #
    wa
    #
    wph
    @58
    @1
    @53
    wcel
    #
    wph
    @35
    @123
    simpll
    @36
    @12
    cA
    @3
    wph
    @32
    @34
    simprl
    #
    sselda
    #
    @97
    @56
    @69
    vk
    cB
    wral
    @125
    esum2d.3
    @97
    @69
    vk
    cB
    wph
    @58
    @66
    @69
    esum2d.4
    anassrs
    ralrimiva
    cB
    cC
    vk
    cW
    vk
    cB
    nfcv
    esumcl
    syl2anc
    #
    syl2anc
    @36
    @3
    @18
    wcel
    #
    wa
    wph
    @58
    @125
    wph
    @35
    @129
    simpll
    @36
    @18
    cA
    @3
    @36
    @17
    cA
    @57
    snssd
    sselda
    @128
    syl2anc
    esumsplit
    adantr
    @36
    @22
    @43
    wceq
    @16
    @36
    @22
    @14
    @41
    cun
    #
    cF
    vz
    cesum
    #
    @43
    @21
    @130
    wceq
    @22
    @131
    wceq
    @21
    @14
    vj
    @18
    @5
    ciun
    #
    cun
    @130
    vj
    @12
    @18
    @5
    iunxun
    @132
    @41
    @14
    @74
    @132
    @41
    wceq
    @75
    vj
    @17
    @5
    @41
    cvv
    vj
    @18
    @40
    @116
    @46
    nfxp
    #
    @48
    @4
    @18
    cB
    @40
    @3
    @17
    sneq
    @49
    xpeq12d
    #
    iunxsngf
    ax-mp
    uneq2i
    eqtri
    @21
    @130
    cF
    vz
    esumeq1
    ax-mp
    @36
    @14
    @41
    cF
    vz
    @36
    vz
    nfv
    vz
    @14
    nfcv
    vz
    @41
    nfcv
    @36
    @117
    @5
    cvv
    wcel
    #
    vj
    @12
    wral
    @14
    cvv
    wcel
    @118
    @36
    @135
    vj
    @12
    @124
    @4
    cvv
    wcel
    @56
    @135
    @3
    snex
    @36
    @123
    @58
    @56
    @127
    @59
    syldan
    @4
    cB
    cvv
    cW
    xpexg
    sylancr
    ralrimiva
    vj
    @12
    @5
    cvv
    cvv
    iunexg
    sylancr
    @36
    @119
    @52
    @41
    cvv
    wcel
    @120
    @60
    @18
    @40
    cvv
    cW
    xpexg
    sylancr
    @36
    vj
    @12
    @5
    @41
    cin
    #
    ciun
    vj
    @12
    c0
    ciun
    @14
    @41
    cin
    c0
    @36
    vj
    @12
    @136
    c0
    @124
    @3
    @17
    wne
    #
    @4
    @18
    cin
    c0
    wceq
    @136
    c0
    wceq
    @124
    @123
    @121
    @137
    @36
    @123
    simpr
    @36
    @121
    @123
    @122
    adantr
    @3
    @17
    @12
    nelne2
    syl2anc
    @3
    @17
    disjsn2
    @4
    @18
    cB
    @40
    xpdisj1
    3syl
    iuneq2dv
    vj
    @12
    @5
    @41
    @133
    iunin1f
    vj
    @12
    iun0
    3eqtr3g
    @36
    @84
    @14
    wcel
    #
    wa
    wph
    @84
    @25
    wcel
    #
    cF
    @53
    wcel
    #
    wph
    @35
    @138
    simpll
    @36
    @14
    @25
    @84
    @36
    @32
    @14
    @25
    wss
    @126
    vj
    @12
    cA
    @5
    iunss1
    syl
    sselda
    wph
    @139
    wa
    #
    @99
    @140
    vj
    cA
    wph
    @139
    vj
    wph
    vj
    nfv
    vj
    vz
    @25
    vj
    cA
    @5
    nfiu1
    nfcri
    nfan
    @141
    @58
    wa
    @99
    wa
    #
    @86
    @140
    vk
    cB
    @142
    vk
    nfv
    vk
    cF
    @53
    esum2d.0
    vk
    @53
    nfcv
    nfel
    @142
    @66
    wa
    #
    @86
    wa
    #
    cF
    cC
    @53
    @86
    @87
    @143
    esum2d.1
    adantl
    @144
    wph
    @58
    @66
    @69
    wph
    @139
    @58
    @99
    @66
    @86
    simp-5l
    @141
    @58
    @99
    @66
    @86
    simp-4r
    @142
    @66
    @86
    simplr
    esum2d.4
    syl12anc
    eqeltrd
    @58
    @99
    @86
    vk
    cB
    wrex
    #
    @141
    @58
    @99
    @145
    vk
    cB
    cA
    @3
    @84
    elsnxp
    biimpa
    adantll
    r19.29af2
    @141
    @139
    @99
    vj
    cA
    wrex
    wph
    @139
    simpr
    vj
    @84
    cA
    @5
    eliun
    sylib
    r19.29af
    #
    syl2anc
    @36
    @84
    @41
    wcel
    #
    wa
    wph
    @139
    @140
    wph
    @35
    @147
    simpll
    @36
    @41
    @25
    @84
    @36
    @55
    @41
    @25
    wss
    @57
    vj
    cA
    @5
    @17
    @41
    vj
    cA
    nfcv
    vj
    @17
    nfcv
    @133
    @134
    ssiun2sf
    syl
    sselda
    @146
    syl2anc
    esumsplit
    syl5eq
    adantr
    3eqtr4d
    ex
    esum2dlem.e
    findcard2d
end
