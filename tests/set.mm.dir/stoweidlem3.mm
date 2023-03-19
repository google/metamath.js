include "c1.mm"
include "cfz.mm"
include "co.mm"
include "wcel.mm"
include "cexp.mm"
include "cfv.mm"
include "clt.mm"
include "wbr.mm"
include "cuz.mm"
include "cn.mm"
include "elnnuz.mm"
include "sylib.mm"
include "eluzfz2.mm"
include "syl.mm"
include "cv.mm"
include "wi.mm"
include "caddc.mm"
include "wceq.mm"
include "oveq2.mm"
include "fveq2.mm"
include "breq12d.mm"
include "imbi2d.mm"
include "weq.mm"
include "wa.mm"
include "cz.mm"
include "w3a.mm"
include "cle.mm"
include "1zzd.mm"
include "nnzd.mm"
include "3jca.mm"
include "1le1.mm"
include "a1i.mm"
include "nnge1d.mm"
include "jca32.mm"
include "elfz2.mm"
include "sylibr.mm"
include "ancli.mm"
include "nfv.mm"
include "nfan.mm"
include "nfcv.mm"
include "nffv.mm"
include "nfbr.mm"
include "nfim.mm"
include "eleq1.mm"
include "anbi2d.mm"
include "breq2d.mm"
include "imbi12d.mm"
include "vtoclg1f.mm"
include "sylc.mm"
include "rpcnd.mm"
include "exp1d.mm"
include "cmul.mm"
include "cseq.mm"
include "fveq1i.mm"
include "1z.mm"
include "seq1.mm"
include "ax-mp.mm"
include "eqtri.mm"
include "3brtr4d.mm"
include "cfzo.mm"
include "crp.mm"
include "3ad2ant3.mm"
include "rpred.mm"
include "cn0.mm"
include "elfzouz.mm"
include "nnnn0.mm"
include "sylbir.mm"
include "3ad2ant1.mm"
include "reexpcld.mm"
include "cr.mm"
include "adantr.mm"
include "nfel1.mm"
include "eleq1d.mm"
include "wf.mm"
include "ad2antlr.mm"
include "elfzelz.mm"
include "adantl.mm"
include "elfzle1.mm"
include "zred.mm"
include "elfzoelz.mm"
include "ad2antrr.mm"
include "nnred.mm"
include "elfzle2.mm"
include "elfzoel2.mm"
include "elfzolt2.mm"
include "ltled.mm"
include "letrd.mm"
include "ffvelrnd.mm"
include "chvar.mm"
include "remulcl.mm"
include "seqcl.mm"
include "syl5eqel.mm"
include "3adant2.mm"
include "fzofzp1.mm"
include "cc0.mm"
include "rpge0d.mm"
include "expge0d.mm"
include "simp3.mm"
include "simp2.mm"
include "mpd.mm"
include "simpr.mm"
include "jca.mm"
include "ltmul12ad.mm"
include "cc.mm"
include "expp1d.mm"
include "seqp1.mm"
include "eqcomd.mm"
include "oveq1d.mm"
include "3eqtrd.mm"
include "3exp.mm"
include "fzind2.mm"
include "mpcom.mm"

theorem stoweidlem3
  let wph: wff ph
  let cA: class A
  let vi: setvar i
  let cF: class F
  let cM: class M
  let cX: class X
  let va: setvar a
  let vm: setvar m
  let vj: setvar j
  let vn: setvar n
  let vk: setvar k
  let vx: setvar x
  assume stoweidlem3.1: |- F/_ i F
  assume stoweidlem3.2: |- F/ i ph
  assume stoweidlem3.3: |- X = seq 1 ( x. , F )
  assume stoweidlem3.4: |- ( ph -> M e. NN )
  assume stoweidlem3.5: |- ( ph -> F : ( 1 ... M ) --> RR )
  assume stoweidlem3.6: |- ( ( ph /\ i e. ( 1 ... M ) ) -> A < ( F ` i ) )
  assume stoweidlem3.7: |- ( ph -> A e. RR+ )

  disjoint A i
  disjoint M i
  disjoint a i
  disjoint a m
  disjoint i m
  disjoint a j
  disjoint M a
  disjoint j m
  disjoint M j
  disjoint M m
  disjoint F a
  disjoint F j
  disjoint a ph
  disjoint j ph
  disjoint m ph
  disjoint A m
  disjoint m n
  disjoint A n
  disjoint X m
  disjoint X n
  disjoint M n
  disjoint n ph
  disjoint k x
  assert |- ( ph -> ( A ^ M ) < ( X ` M ) )

  proof
    cM
    c1
    cM
    cfz
    co
    #
    wcel
    #
    wph
    cA
    cM
    cexp
    co
    #
    cM
    cX
    cfv
    #
    clt
    wbr
    #
    wph
    cM
    c1
    cuz
    cfv
    #
    wcel
    #
    @1
    wph
    cM
    cn
    wcel
    @6
    stoweidlem3.4
    cM
    elnnuz
    sylib
    c1
    cM
    eluzfz2
    syl
    wph
    cA
    vn
    cv
    #
    cexp
    co
    #
    @7
    cX
    cfv
    #
    clt
    wbr
    #
    wi
    wph
    cA
    c1
    cexp
    co
    #
    c1
    cX
    cfv
    #
    clt
    wbr
    #
    wi
    #
    wph
    cA
    vm
    cv
    #
    cexp
    co
    #
    @15
    cX
    cfv
    #
    clt
    wbr
    #
    wi
    #
    wph
    cA
    @15
    c1
    caddc
    co
    #
    cexp
    co
    #
    @20
    cX
    cfv
    #
    clt
    wbr
    #
    wi
    wph
    @4
    wi
    vn
    vm
    cM
    c1
    cM
    @7
    c1
    wceq
    #
    @10
    @13
    wph
    @24
    @8
    @11
    @9
    @12
    clt
    @7
    c1
    cA
    cexp
    oveq2
    @7
    c1
    cX
    fveq2
    breq12d
    imbi2d
    vn
    vm
    weq
    #
    @10
    @18
    wph
    @25
    @8
    @16
    @9
    @17
    clt
    @7
    @15
    cA
    cexp
    oveq2
    @7
    @15
    cX
    fveq2
    breq12d
    imbi2d
    @7
    @20
    wceq
    #
    @10
    @23
    wph
    @26
    @8
    @21
    @9
    @22
    clt
    @7
    @20
    cA
    cexp
    oveq2
    @7
    @20
    cX
    fveq2
    breq12d
    imbi2d
    @7
    cM
    wceq
    #
    @10
    @4
    wph
    @27
    @8
    @2
    @9
    @3
    clt
    @7
    cM
    cA
    cexp
    oveq2
    @7
    cM
    cX
    fveq2
    breq12d
    imbi2d
    @14
    @6
    wph
    cA
    c1
    cF
    cfv
    #
    @11
    @12
    clt
    wph
    c1
    @0
    wcel
    #
    wph
    @29
    wa
    #
    cA
    @28
    clt
    wbr
    #
    wph
    c1
    cz
    wcel
    #
    cM
    cz
    wcel
    #
    @32
    w3a
    #
    c1
    c1
    cle
    wbr
    #
    c1
    cM
    cle
    wbr
    #
    wa
    wa
    @29
    wph
    @34
    @35
    @36
    wph
    @32
    @33
    @32
    wph
    1zzd
    #
    wph
    cM
    stoweidlem3.4
    nnzd
    #
    @37
    3jca
    @35
    wph
    1le1
    a1i
    wph
    cM
    stoweidlem3.4
    nnge1d
    jca32
    c1
    c1
    cM
    elfz2
    sylibr
    #
    wph
    @29
    @39
    ancli
    wph
    vi
    cv
    #
    @0
    wcel
    #
    wa
    #
    cA
    @40
    cF
    cfv
    #
    clt
    wbr
    #
    wi
    #
    @30
    @31
    wi
    vi
    c1
    @0
    @30
    @31
    vi
    wph
    @29
    vi
    stoweidlem3.2
    @29
    vi
    nfv
    nfan
    vi
    cA
    @28
    clt
    vi
    cA
    nfcv
    #
    vi
    clt
    nfcv
    #
    vi
    c1
    cF
    stoweidlem3.1
    vi
    c1
    nfcv
    nffv
    nfbr
    nfim
    @40
    c1
    wceq
    #
    @42
    @30
    @44
    @31
    @48
    @41
    @29
    wph
    @40
    c1
    @0
    eleq1
    anbi2d
    @48
    @43
    @28
    cA
    clt
    @40
    c1
    cF
    fveq2
    breq2d
    imbi12d
    stoweidlem3.6
    vtoclg1f
    sylc
    wph
    cA
    wph
    cA
    stoweidlem3.7
    rpcnd
    #
    exp1d
    @12
    @28
    wceq
    wph
    @12
    c1
    cmul
    cF
    c1
    cseq
    #
    cfv
    #
    @28
    c1
    cX
    @50
    stoweidlem3.3
    fveq1i
    @32
    @51
    @28
    wceq
    1z
    cmul
    cF
    c1
    seq1
    ax-mp
    eqtri
    a1i
    3brtr4d
    a1i
    @15
    c1
    cM
    cfzo
    co
    wcel
    #
    @19
    wph
    @23
    @52
    @19
    wph
    w3a
    #
    @16
    cA
    cmul
    co
    @17
    @20
    cF
    cfv
    #
    cmul
    co
    #
    @21
    @22
    clt
    @53
    @16
    @17
    cA
    @54
    @53
    cA
    @15
    @53
    cA
    wph
    @52
    cA
    crp
    wcel
    @19
    stoweidlem3.7
    3ad2ant3
    rpred
    #
    @52
    @19
    @15
    cn0
    wcel
    #
    wph
    @52
    @15
    @5
    wcel
    #
    @57
    @15
    c1
    cM
    elfzouz
    #
    @58
    @15
    cn
    wcel
    @57
    @15
    elnnuz
    @15
    nnnn0
    sylbir
    syl
    3ad2ant1
    #
    reexpcld
    @52
    wph
    @17
    cr
    wcel
    @19
    @52
    wph
    wa
    #
    @17
    @15
    @50
    cfv
    #
    cr
    @15
    cX
    @50
    stoweidlem3.3
    fveq1i
    #
    @61
    va
    vj
    cmul
    cr
    cF
    c1
    @15
    @52
    @58
    wph
    @59
    adantr
    @61
    @40
    c1
    @15
    cfz
    co
    #
    wcel
    #
    wa
    #
    @43
    cr
    wcel
    #
    wi
    @61
    va
    cv
    #
    @64
    wcel
    #
    wa
    #
    @68
    cF
    cfv
    #
    cr
    wcel
    #
    wi
    vi
    va
    @70
    @72
    vi
    @61
    @69
    vi
    @52
    wph
    vi
    @52
    vi
    nfv
    stoweidlem3.2
    nfan
    @69
    vi
    nfv
    nfan
    vi
    @71
    cr
    vi
    @68
    cF
    stoweidlem3.1
    vi
    @68
    nfcv
    nffv
    nfel1
    nfim
    vi
    va
    weq
    #
    @66
    @70
    @67
    @72
    @73
    @65
    @69
    @61
    @40
    @68
    @64
    eleq1
    anbi2d
    @73
    @43
    @71
    cr
    @40
    @68
    cF
    fveq2
    eleq1d
    imbi12d
    @66
    @0
    cr
    @40
    cF
    wph
    @0
    cr
    cF
    wf
    #
    @52
    @65
    stoweidlem3.5
    ad2antlr
    @66
    @32
    @33
    @40
    cz
    wcel
    #
    w3a
    #
    c1
    @40
    cle
    wbr
    #
    @40
    cM
    cle
    wbr
    #
    wa
    wa
    @41
    @66
    @76
    @77
    @78
    @66
    @32
    @33
    @75
    @66
    1zzd
    wph
    @33
    @52
    @65
    @38
    ad2antlr
    @65
    @75
    @61
    @40
    c1
    @15
    elfzelz
    #
    adantl
    3jca
    @65
    @77
    @61
    @40
    c1
    @15
    elfzle1
    adantl
    @66
    @40
    @15
    cM
    @65
    @40
    cr
    wcel
    @61
    @65
    @40
    @79
    zred
    adantl
    @52
    @15
    cr
    wcel
    wph
    @65
    @52
    @15
    @15
    c1
    cM
    elfzoelz
    zred
    #
    ad2antrr
    wph
    cM
    cr
    wcel
    @52
    @65
    wph
    cM
    stoweidlem3.4
    nnred
    ad2antlr
    @65
    @40
    @15
    cle
    wbr
    @61
    @40
    c1
    @15
    elfzle2
    adantl
    @52
    @15
    cM
    cle
    wbr
    wph
    @65
    @52
    @15
    cM
    @80
    @52
    cM
    @15
    c1
    cM
    elfzoel2
    zred
    @15
    c1
    cM
    elfzolt2
    ltled
    ad2antrr
    letrd
    jca32
    @40
    c1
    cM
    elfz2
    sylibr
    ffvelrnd
    chvar
    @68
    cr
    wcel
    vj
    cv
    #
    cr
    wcel
    wa
    @68
    @81
    cmul
    co
    cr
    wcel
    @61
    @68
    @81
    remulcl
    adantl
    seqcl
    syl5eqel
    3adant2
    @56
    @53
    @0
    cr
    @20
    cF
    wph
    @52
    @74
    @19
    stoweidlem3.5
    3ad2ant3
    @52
    @19
    @20
    @0
    wcel
    #
    wph
    c1
    cM
    @15
    fzofzp1
    #
    3ad2ant1
    ffvelrnd
    @53
    cA
    @15
    @56
    @60
    wph
    @52
    cc0
    cA
    cle
    wbr
    @19
    wph
    cA
    stoweidlem3.7
    rpge0d
    3ad2ant3
    #
    expge0d
    @53
    wph
    @18
    @52
    @19
    wph
    simp3
    @52
    @19
    wph
    simp2
    mpd
    @84
    @52
    wph
    cA
    @54
    clt
    wbr
    #
    @19
    @61
    @82
    wph
    @82
    wa
    #
    @85
    @52
    @82
    wph
    @83
    adantr
    #
    @61
    wph
    @82
    @52
    wph
    simpr
    @87
    jca
    @45
    @86
    @85
    wi
    vi
    @20
    @0
    @86
    @85
    vi
    wph
    @82
    vi
    stoweidlem3.2
    @82
    vi
    nfv
    nfan
    vi
    cA
    @54
    clt
    @46
    @47
    vi
    @20
    cF
    stoweidlem3.1
    vi
    @20
    nfcv
    nffv
    nfbr
    nfim
    @40
    @20
    wceq
    #
    @42
    @86
    @44
    @85
    @88
    @41
    @82
    wph
    @40
    @20
    @0
    eleq1
    anbi2d
    @88
    @43
    @54
    cA
    clt
    @40
    @20
    cF
    fveq2
    breq2d
    imbi12d
    stoweidlem3.6
    vtoclg1f
    sylc
    3adant2
    ltmul12ad
    @53
    cA
    @15
    wph
    @52
    cA
    cc
    wcel
    @19
    @49
    3ad2ant3
    @60
    expp1d
    @53
    @22
    @20
    @50
    cfv
    #
    @62
    @54
    cmul
    co
    #
    @55
    @22
    @89
    wceq
    @53
    @20
    cX
    @50
    stoweidlem3.3
    fveq1i
    a1i
    @53
    @58
    @89
    @90
    wceq
    @52
    @19
    @58
    wph
    @59
    3ad2ant1
    cmul
    cF
    c1
    @15
    seqp1
    syl
    @53
    @62
    @17
    @54
    cmul
    @53
    @17
    @62
    @17
    @62
    wceq
    @53
    @63
    a1i
    eqcomd
    oveq1d
    3eqtrd
    3brtr4d
    3exp
    fzind2
    mpcom
end
