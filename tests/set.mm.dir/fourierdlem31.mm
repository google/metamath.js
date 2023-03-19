include "c0.mm"
include "wceq.mm"
include "wral.mm"
include "cv.mm"
include "cpnf.mm"
include "cioo.mm"
include "co.mm"
include "cn.mm"
include "wrex.mm"
include "c1.mm"
include "wcel.mm"
include "1nn.mm"
include "rzal.mm"
include "ralrimivw.mm"
include "oveq1.mm"
include "raleqdv.mm"
include "rspcev.mm"
include "sylancr.mm"
include "adantl.mm"
include "wn.mm"
include "wa.mm"
include "crn.mm"
include "cr.mm"
include "clt.mm"
include "csup.mm"
include "wss.mm"
include "cinf.mm"
include "crab.mm"
include "a1i.mm"
include "infeq1d.mm"
include "ssrab2.mm"
include "cuz.mm"
include "cfv.mm"
include "wne.mm"
include "nnuz.mm"
include "sseqtri.mm"
include "r19.21bi.mm"
include "rabn0.mm"
include "sylibr.mm"
include "infssuzcl.mm"
include "sseldi.mm"
include "eqeltrd.mm"
include "ex.mm"
include "ralrimi.mm"
include "rnmptss.mm"
include "syl.mm"
include "adantr.mm"
include "wor.mm"
include "cfn.mm"
include "ltso.mm"
include "cmpt.mm"
include "mptfi.mm"
include "syl5eqel.mm"
include "rnfi.mm"
include "wex.mm"
include "neqne.mm"
include "n0.mm"
include "sylib.mm"
include "nfv.mm"
include "nfan.mm"
include "nfrn.mm"
include "nfcv.mm"
include "nfne.mm"
include "wi.mm"
include "simpr.mm"
include "elrnmpt1.mm"
include "syl2anc.mm"
include "ne0i.mm"
include "exlimd.mm"
include "mpd.mm"
include "nnssre.mm"
include "syl6ss.mm"
include "fisupcl.mm"
include "syl13anc.mm"
include "sseldd.mm"
include "nfsup.mm"
include "nfcxfr.mm"
include "nfov.mm"
include "nfcri.mm"
include "cxr.mm"
include "fvmpt2.mm"
include "nnxrd.mm"
include "pnfxr.mm"
include "elioore.mm"
include "nnred.mm"
include "neneqd.mm"
include "syldan.mm"
include "cle.mm"
include "wbr.mm"
include "fimaxre2.mm"
include "suprub.mm"
include "syl31anc.mm"
include "syl6breqr.mm"
include "rexrd.mm"
include "ioogtlb.mm"
include "syl3anc.mm"
include "lelttrd.mm"
include "ltpnfd.mm"
include "eliood.mm"
include "wb.mm"
include "nfrab1.mm"
include "nfinf.mm"
include "nfmpt.mm"
include "nffv.mm"
include "nfel.mm"
include "nfel1.mm"
include "nfral.mm"
include "nfbi.mm"
include "eleq1.mm"
include "nfra1.mm"
include "nfrab.mm"
include "raleqf.mm"
include "anbi12d.mm"
include "bibi12d.mm"
include "rabid.mm"
include "vtoclgf.mm"
include "mpbid.mm"
include "simprd.mm"
include "an32s.mm"
include "pm2.61dan.mm"

theorem fourierdlem31
  let wph: wff ph
  let wch: wff ch
  let cA: class A
  let vi: setvar i
  let vm: setvar m
  let vn: setvar n
  let cM: class M
  let cN: class N
  let cV: class V
  let vr: setvar r
  let vx: setvar x
  let vy: setvar y
  let vk: setvar k
  assume fourierdlem31.i: |- F/ i ph
  assume fourierdlem31.r: |- F/ r ph
  assume fourierdlem31.iv: |- F/_ i V
  assume fourierdlem31.a: |- ( ph -> A e. Fin )
  assume fourierdlem31.exm: |- ( ph -> A. i e. A E. m e. NN A. r e. ( m (,) +oo ) ch )
  assume fourierdlem31.m: |- M = { m e. NN | A. r e. ( m (,) +oo ) ch }
  assume fourierdlem31.v: |- V = ( i e. A |-> inf ( M , RR , < ) )
  assume fourierdlem31.n: |- N = sup ( ran V , RR , < )

  disjoint A i
  disjoint A m
  disjoint A r
  disjoint i m
  disjoint i r
  disjoint m r
  disjoint A n
  disjoint i n
  disjoint n r
  disjoint N n
  disjoint ch m
  disjoint ch n
  disjoint V x
  disjoint V y
  disjoint x y
  disjoint k x
  assert |- ( ph -> E. n e. NN A. r e. ( n (,) +oo ) A. i e. A ch )

  proof
    wph
    cA
    c0
    wceq
    #
    wch
    vi
    cA
    wral
    #
    vr
    vn
    cv
    #
    cpnf
    cioo
    co
    #
    wral
    #
    vn
    cn
    wrex
    #
    @0
    @5
    wph
    @0
    c1
    cn
    wcel
    @1
    vr
    c1
    cpnf
    cioo
    co
    #
    wral
    #
    @5
    1nn
    @0
    @1
    vr
    @6
    wch
    vi
    cA
    rzal
    ralrimivw
    @4
    @7
    vn
    c1
    cn
    @2
    c1
    wceq
    @1
    vr
    @3
    @6
    @2
    c1
    cpnf
    cioo
    oveq1
    raleqdv
    rspcev
    sylancr
    adantl
    wph
    @0
    wn
    #
    wa
    #
    cN
    cn
    wcel
    #
    @1
    vr
    cN
    cpnf
    cioo
    co
    #
    wral
    #
    @5
    @9
    cN
    cV
    crn
    #
    cr
    clt
    csup
    #
    cn
    fourierdlem31.n
    @9
    @13
    cn
    @14
    wph
    @13
    cn
    wss
    #
    @8
    wph
    cM
    cr
    clt
    cinf
    #
    cn
    wcel
    #
    vi
    cA
    wral
    @15
    wph
    @17
    vi
    cA
    fourierdlem31.i
    wph
    vi
    cv
    #
    cA
    wcel
    #
    @17
    wph
    @19
    wa
    #
    @16
    wch
    vr
    vm
    cv
    #
    cpnf
    cioo
    co
    #
    wral
    #
    vm
    cn
    crab
    #
    cr
    clt
    cinf
    #
    cn
    @20
    cr
    cM
    @24
    clt
    cM
    @24
    wceq
    @20
    fourierdlem31.m
    a1i
    infeq1d
    #
    @20
    @24
    cn
    @25
    @23
    vm
    cn
    ssrab2
    #
    @20
    @24
    c1
    cuz
    cfv
    #
    wss
    @24
    c0
    wne
    #
    @25
    @24
    wcel
    @24
    cn
    @28
    @27
    nnuz
    sseqtri
    @20
    @23
    vm
    cn
    wrex
    #
    @29
    wph
    @30
    vi
    cA
    fourierdlem31.exm
    r19.21bi
    @23
    vm
    cn
    rabn0
    sylibr
    @24
    c1
    infssuzcl
    sylancr
    #
    sseldi
    eqeltrd
    #
    ex
    ralrimi
    vi
    cA
    @16
    cn
    cV
    fourierdlem31.v
    rnmptss
    syl
    #
    adantr
    #
    @9
    cr
    clt
    wor
    #
    @13
    cfn
    wcel
    #
    @13
    c0
    wne
    #
    @13
    cr
    wss
    #
    @14
    @13
    wcel
    @35
    @9
    ltso
    a1i
    wph
    @36
    @8
    wph
    cV
    cfn
    wcel
    @36
    wph
    cV
    vi
    cA
    @16
    cmpt
    #
    cfn
    fourierdlem31.v
    wph
    cA
    cfn
    wcel
    @39
    cfn
    wcel
    fourierdlem31.a
    vi
    cA
    @16
    mptfi
    syl
    syl5eqel
    cV
    rnfi
    syl
    #
    adantr
    @9
    @19
    vi
    wex
    #
    @37
    @8
    @41
    wph
    @8
    cA
    c0
    wne
    #
    @41
    cA
    c0
    neqne
    vi
    cA
    n0
    sylib
    adantl
    @9
    @19
    @37
    vi
    wph
    @8
    vi
    fourierdlem31.i
    @8
    vi
    nfv
    nfan
    vi
    @13
    c0
    vi
    cV
    fourierdlem31.iv
    nfrn
    #
    vi
    c0
    nfcv
    nfne
    wph
    @19
    @37
    wi
    @8
    wph
    @19
    @37
    @20
    @16
    @13
    wcel
    #
    @37
    @20
    @19
    @17
    @44
    wph
    @19
    simpr
    #
    @32
    vi
    cA
    @16
    cV
    cn
    fourierdlem31.v
    elrnmpt1
    syl2anc
    #
    @13
    @16
    ne0i
    syl
    #
    ex
    adantr
    exlimd
    mpd
    @9
    @13
    cn
    cr
    @34
    nnssre
    syl6ss
    #
    cr
    @13
    clt
    fisupcl
    syl13anc
    sseldd
    syl5eqel
    #
    wph
    @12
    @8
    wph
    @1
    vr
    @11
    fourierdlem31.r
    wph
    vr
    cv
    #
    @11
    wcel
    #
    @1
    wph
    @51
    wa
    #
    wch
    vi
    cA
    wph
    @51
    vi
    fourierdlem31.i
    vi
    vr
    @11
    vi
    cN
    cpnf
    cioo
    vi
    cN
    @14
    fourierdlem31.n
    vi
    @13
    cr
    clt
    @43
    vi
    cr
    nfcv
    vi
    clt
    nfcv
    nfsup
    nfcxfr
    vi
    cioo
    nfcv
    vi
    cpnf
    nfcv
    nfov
    nfcri
    nfan
    @52
    @19
    wch
    wph
    @19
    @51
    wch
    @20
    @51
    @50
    @18
    cV
    cfv
    #
    cpnf
    cioo
    co
    #
    wcel
    wch
    @20
    @51
    wa
    #
    @53
    cpnf
    @50
    @20
    @53
    cxr
    wcel
    @51
    @20
    @53
    @16
    cxr
    @20
    @19
    @17
    @53
    @16
    wceq
    @45
    @32
    vi
    cA
    @16
    cn
    cV
    fourierdlem31.v
    fvmpt2
    syl2anc
    #
    @20
    @16
    @32
    nnxrd
    eqeltrd
    adantr
    cpnf
    cxr
    wcel
    #
    @55
    pnfxr
    a1i
    #
    @51
    @50
    cr
    wcel
    @20
    @50
    cN
    cpnf
    elioore
    adantl
    #
    @55
    @53
    cN
    @50
    @20
    @53
    cr
    wcel
    @51
    @20
    @53
    @20
    @53
    @16
    cn
    @56
    @32
    eqeltrd
    #
    nnred
    adantr
    @20
    cN
    cr
    wcel
    @51
    @20
    cN
    wph
    @19
    @8
    @10
    @20
    cA
    c0
    @19
    @42
    wph
    cA
    @18
    ne0i
    adantl
    neneqd
    #
    @49
    syldan
    nnred
    adantr
    #
    @59
    @20
    @53
    cN
    cle
    wbr
    @51
    @20
    @53
    @14
    cN
    cle
    @20
    @38
    @37
    vy
    cv
    vx
    cv
    cle
    wbr
    vy
    @13
    wral
    vx
    cr
    wrex
    #
    @53
    @13
    wcel
    @53
    @14
    cle
    wbr
    wph
    @19
    @8
    @38
    @61
    @48
    syldan
    @47
    wph
    @63
    @19
    wph
    @38
    @36
    @63
    wph
    @13
    cn
    cr
    @33
    nnssre
    syl6ss
    @40
    vx
    vy
    @13
    fimaxre2
    syl2anc
    adantr
    @20
    @53
    @16
    @13
    @56
    @46
    eqeltrd
    vx
    vy
    @13
    @53
    suprub
    syl31anc
    fourierdlem31.n
    syl6breqr
    adantr
    @55
    cN
    cxr
    wcel
    @57
    @51
    cN
    @50
    clt
    wbr
    @55
    cN
    @62
    rexrd
    @58
    @20
    @51
    simpr
    cN
    cpnf
    @50
    ioogtlb
    syl3anc
    lelttrd
    @55
    @50
    @59
    ltpnfd
    eliood
    @20
    wch
    vr
    @54
    @20
    @53
    cn
    wcel
    #
    wch
    vr
    @54
    wral
    #
    @20
    @53
    @24
    wcel
    #
    @64
    @65
    wa
    #
    @20
    @53
    @16
    @24
    @56
    @20
    @16
    @25
    @24
    @26
    @31
    eqeltrd
    eqeltrd
    @20
    @64
    @66
    @67
    wb
    #
    @60
    @21
    @24
    wcel
    #
    @21
    cn
    wcel
    #
    @23
    wa
    #
    wb
    @68
    vm
    @53
    cn
    vm
    @18
    cV
    vm
    cV
    @39
    fourierdlem31.v
    vm
    vi
    cA
    @16
    vm
    cA
    nfcv
    vm
    cM
    cr
    clt
    vm
    cM
    @24
    fourierdlem31.m
    @23
    vm
    cn
    nfrab1
    #
    nfcxfr
    vm
    cr
    nfcv
    vm
    clt
    nfcv
    nfinf
    nfmpt
    nfcxfr
    vm
    @18
    nfcv
    nffv
    #
    @66
    @67
    vm
    vm
    @53
    @24
    @73
    @72
    nfel
    @64
    @65
    vm
    vm
    @53
    cn
    @73
    nfel1
    wch
    vm
    vr
    @54
    vm
    @53
    cpnf
    cioo
    @73
    vm
    cioo
    nfcv
    vm
    cpnf
    nfcv
    nfov
    wch
    vm
    nfv
    nfral
    nfan
    nfbi
    @21
    @53
    wceq
    #
    @69
    @66
    @71
    @67
    @21
    @53
    @24
    eleq1
    @74
    @70
    @64
    @23
    @65
    @21
    @53
    cn
    eleq1
    @74
    @22
    @54
    wceq
    @23
    @65
    wb
    @21
    @53
    cpnf
    cioo
    oveq1
    wch
    vr
    @22
    @54
    vr
    @22
    nfcv
    vr
    @53
    cpnf
    cioo
    vr
    @18
    cV
    vr
    cV
    @39
    fourierdlem31.v
    vr
    vi
    cA
    @16
    vr
    cA
    nfcv
    vr
    cM
    cr
    clt
    vr
    cM
    @24
    fourierdlem31.m
    @23
    vr
    vm
    cn
    wch
    vr
    @22
    nfra1
    vr
    cn
    nfcv
    nfrab
    nfcxfr
    vr
    cr
    nfcv
    #
    vr
    clt
    nfcv
    #
    nfinf
    nfmpt
    nfcxfr
    #
    vr
    @18
    nfcv
    nffv
    vr
    cioo
    nfcv
    #
    vr
    cpnf
    nfcv
    #
    nfov
    raleqf
    syl
    anbi12d
    bibi12d
    @23
    vm
    cn
    rabid
    vtoclgf
    syl
    mpbid
    simprd
    r19.21bi
    syldan
    an32s
    ex
    ralrimi
    ex
    ralrimi
    adantr
    @4
    @12
    vn
    cN
    cn
    @2
    cN
    wceq
    @3
    @11
    wceq
    @4
    @12
    wb
    @2
    cN
    cpnf
    cioo
    oveq1
    @1
    vr
    @3
    @11
    vr
    @3
    nfcv
    vr
    cN
    cpnf
    cioo
    vr
    cN
    @14
    fourierdlem31.n
    vr
    @13
    cr
    clt
    vr
    cV
    @77
    nfrn
    @75
    @76
    nfsup
    nfcxfr
    @78
    @79
    nfov
    raleqf
    syl
    rspcev
    syl2anc
    pm2.61dan
end
