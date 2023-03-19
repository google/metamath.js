include "cmin.mm"
include "co.mm"
include "wceq.mm"
include "wa.mm"
include "cfv.mm"
include "c1.mm"
include "caddc.mm"
include "csn.mm"
include "cpr.mm"
include "wss.mm"
include "wif.mm"
include "chash.mm"
include "cmo.mm"
include "cc0.mm"
include "cv.mm"
include "cfzo.mm"
include "wb.mm"
include "oveq1.mm"
include "0p1e1.mm"
include "syl6eq.mm"
include "wkslem2.mm"
include "mpdan.mm"
include "cn.mm"
include "wcel.mm"
include "clt.mm"
include "wbr.mm"
include "w3a.mm"
include "elfzo1.mm"
include "simp2.mm"
include "sylbi.mm"
include "syl.mm"
include "lbfzo0.mm"
include "sylibr.mm"
include "rspcdva.mm"
include "eqeq1.mm"
include "sneq.mm"
include "eqeq2d.mm"
include "preq1.mm"
include "sseq1d.mm"
include "ifpbi123d.mm"
include "mpbird.mm"
include "cc.mm"
include "nncn.mm"
include "npcan.mm"
include "syl2anr.mm"
include "simpr.mm"
include "eqcomi.mm"
include "a1i.mm"
include "oveq2d.mm"
include "crp.mm"
include "nnrp.mm"
include "modid0.mm"
include "adantl.mm"
include "eqtrd.mm"
include "sylan9eqr.mm"
include "simpl.mm"
include "3jca.mm"
include "3adant3.mm"
include "simp1.mm"
include "fveq2d.mm"
include "eqeq1d.mm"
include "sneqd.mm"
include "eqeq12d.mm"
include "preq1d.mm"
include "sseq12d.mm"
include "3syl.mm"
include "cfz.mm"
include "cn0.mm"
include "nnsub.mm"
include "biimp3a.mm"
include "nnnn0d.mm"
include "nn0fz0.mm"
include "sylib.mm"
include "crctcshwlkn0lem2.mm"
include "cuz.mm"
include "cz.mm"
include "cle.mm"
include "elfzoel2.mm"
include "elfzoelz.mm"
include "zsubcld.mm"
include "peano2zd.mm"
include "cr.mm"
include "nnre.mm"
include "anim1i.mm"
include "ancoms.mm"
include "crctcshwlkn0lem1.mm"
include "eluz2.mm"
include "eluzfz1.mm"
include "crctcshwlkn0lem3.mm"
include "subcl.mm"
include "ax-1cn.mm"
include "pncan2.mm"
include "eqcomd.mm"
include "sylancl.mm"
include "peano2cn.mm"
include "subsub3d.mm"
include "eqtr2d.mm"
include "syl2an.mm"
include "ccsh.mm"
include "fveq1i.mm"
include "cword.mm"
include "adantr.mm"
include "elfzofz.mm"
include "ubmelfzo.mm"
include "oveq2i.mm"
include "syl6eleqr.mm"
include "cshwidxmod.mm"
include "syl3anc.mm"
include "syl5eq.mm"
include "simp3.mm"
include "preq12d.mm"
include "wkslem1.mm"

theorem crctcshwlkn0lem6
  let wph: wff ph
  let vx: setvar x
  let cA: class A
  let cP: class P
  let cQ: class Q
  let cS: class S
  let vi: setvar i
  let cF: class F
  let cH: class H
  let cI: class I
  let cJ: class J
  let cN: class N
  let vj: setvar j
  assume crctcshwlkn0lem.s: |- ( ph -> S e. ( 1 ..^ N ) )
  assume crctcshwlkn0lem.q: |- Q = ( x e. ( 0 ... N ) |-> if ( x <_ ( N - S ) , ( P ` ( x + S ) ) , ( P ` ( ( x + S ) - N ) ) ) )
  assume crctcshwlkn0lem.h: |- H = ( F cyclShift S )
  assume crctcshwlkn0lem.n: |- N = ( # ` F )
  assume crctcshwlkn0lem.f: |- ( ph -> F e. Word A )
  assume crctcshwlkn0lem.p: |- ( ph -> A. i e. ( 0 ..^ N ) if- ( ( P ` i ) = ( P ` ( i + 1 ) ) , ( I ` ( F ` i ) ) = { ( P ` i ) } , { ( P ` i ) , ( P ` ( i + 1 ) ) } C_ ( I ` ( F ` i ) ) ) )
  assume crctcshwlkn0lem.e: |- ( ph -> ( P ` N ) = ( P ` 0 ) )

  disjoint J x
  disjoint N x
  disjoint P x
  disjoint S x
  disjoint ph x
  disjoint F i
  disjoint I i
  disjoint N i
  disjoint P i
  disjoint S i
  disjoint i ph
  disjoint j ph
  disjoint i j
  disjoint j x
  assert |- ( ( ph /\ J = ( N - S ) ) -> if- ( ( Q ` J ) = ( Q ` ( J + 1 ) ) , ( I ` ( H ` J ) ) = { ( Q ` J ) } , { ( Q ` J ) , ( Q ` ( J + 1 ) ) } C_ ( I ` ( H ` J ) ) ) )

  proof
    wph
    cJ
    cN
    cS
    cmin
    co
    #
    wceq
    #
    wa
    cJ
    cQ
    cfv
    #
    cJ
    c1
    caddc
    co
    cQ
    cfv
    #
    wceq
    cJ
    cH
    cfv
    cI
    cfv
    #
    @2
    csn
    wceq
    @2
    @3
    cpr
    @4
    wss
    wif
    #
    @0
    cQ
    cfv
    #
    @0
    c1
    caddc
    co
    #
    cQ
    cfv
    #
    wceq
    #
    @0
    cH
    cfv
    #
    cI
    cfv
    #
    @6
    csn
    #
    wceq
    #
    @6
    @8
    cpr
    #
    @11
    wss
    #
    wif
    #
    wph
    @16
    @1
    wph
    @16
    @0
    cS
    caddc
    co
    #
    cP
    cfv
    #
    c1
    cP
    cfv
    #
    wceq
    #
    @17
    cF
    chash
    cfv
    #
    cmo
    co
    #
    cF
    cfv
    #
    cI
    cfv
    #
    @18
    csn
    #
    wceq
    #
    @18
    @19
    cpr
    #
    @24
    wss
    #
    wif
    #
    wph
    @29
    cN
    cP
    cfv
    #
    @19
    wceq
    #
    cc0
    cF
    cfv
    #
    cI
    cfv
    #
    @30
    csn
    #
    wceq
    #
    @30
    @19
    cpr
    #
    @33
    wss
    #
    wif
    #
    wph
    @38
    cc0
    cP
    cfv
    #
    @19
    wceq
    #
    @33
    @39
    csn
    #
    wceq
    #
    @39
    @19
    cpr
    #
    @33
    wss
    #
    wif
    #
    wph
    vi
    cv
    #
    cP
    cfv
    #
    @46
    c1
    caddc
    co
    #
    cP
    cfv
    #
    wceq
    @46
    cF
    cfv
    cI
    cfv
    #
    @47
    csn
    wceq
    @47
    @49
    cpr
    @50
    wss
    wif
    #
    @45
    vi
    cc0
    cN
    cfzo
    co
    #
    cc0
    @46
    cc0
    wceq
    #
    @48
    c1
    wceq
    @51
    @45
    wb
    @53
    @48
    cc0
    c1
    caddc
    co
    c1
    @46
    cc0
    c1
    caddc
    oveq1
    0p1e1
    syl6eq
    @46
    cc0
    c1
    cP
    cF
    cI
    wkslem2
    mpdan
    crctcshwlkn0lem.p
    wph
    cN
    cn
    wcel
    #
    cc0
    @52
    wcel
    wph
    cS
    c1
    cN
    cfzo
    co
    wcel
    #
    @54
    crctcshwlkn0lem.s
    @55
    cS
    cn
    wcel
    #
    @54
    cS
    cN
    clt
    wbr
    #
    w3a
    #
    @54
    cN
    cS
    elfzo1
    #
    @56
    @54
    @57
    simp2
    sylbi
    syl
    cN
    lbfzo0
    sylibr
    rspcdva
    wph
    @30
    @39
    wceq
    #
    @38
    @45
    wb
    crctcshwlkn0lem.e
    @60
    @31
    @35
    @37
    @40
    @42
    @44
    @30
    @39
    @19
    eqeq1
    @60
    @34
    @41
    @33
    @30
    @39
    sneq
    eqeq2d
    @60
    @36
    @43
    @33
    @30
    @39
    @19
    preq1
    sseq1d
    ifpbi123d
    syl
    mpbird
    wph
    @55
    @17
    cN
    wceq
    #
    @22
    cc0
    wceq
    #
    @56
    @54
    wa
    #
    w3a
    #
    @29
    @38
    wb
    crctcshwlkn0lem.s
    @55
    @58
    @64
    @59
    @56
    @54
    @64
    @57
    @63
    @61
    @64
    @54
    cN
    cc
    wcel
    #
    cS
    cc
    wcel
    #
    @61
    @56
    cN
    nncn
    #
    cS
    nncn
    #
    cN
    cS
    npcan
    syl2anr
    @63
    @61
    wa
    @61
    @62
    @63
    @63
    @61
    simpr
    @61
    @63
    @22
    cN
    @21
    cmo
    co
    #
    cc0
    @17
    cN
    @21
    cmo
    oveq1
    @63
    @69
    cN
    cN
    cmo
    co
    #
    cc0
    @63
    @21
    cN
    cN
    cmo
    @21
    cN
    wceq
    @63
    cN
    @21
    crctcshwlkn0lem.n
    eqcomi
    #
    a1i
    oveq2d
    @54
    @70
    cc0
    wceq
    #
    @56
    @54
    cN
    crp
    wcel
    @72
    cN
    nnrp
    cN
    modid0
    syl
    adantl
    eqtrd
    sylan9eqr
    @63
    @61
    simpl
    3jca
    mpdan
    3adant3
    sylbi
    @64
    @20
    @26
    @28
    @31
    @35
    @37
    @64
    @18
    @30
    @19
    @64
    @17
    cN
    cP
    @61
    @62
    @63
    simp1
    fveq2d
    #
    eqeq1d
    @64
    @24
    @33
    @25
    @34
    @64
    @23
    @32
    cI
    @64
    @22
    cc0
    cF
    @61
    @62
    @63
    simp2
    fveq2d
    fveq2d
    #
    @64
    @18
    @30
    @73
    sneqd
    eqeq12d
    @64
    @27
    @36
    @24
    @33
    @64
    @18
    @30
    @19
    @73
    preq1d
    @74
    sseq12d
    ifpbi123d
    3syl
    mpbird
    wph
    @6
    @18
    wceq
    #
    @8
    @19
    wceq
    #
    @10
    @23
    wceq
    #
    @16
    @29
    wb
    wph
    @0
    cc0
    @0
    cfz
    co
    wcel
    #
    @75
    wph
    @0
    cn0
    wcel
    #
    @78
    wph
    @55
    @79
    crctcshwlkn0lem.s
    @55
    @58
    @79
    @59
    @58
    @0
    @56
    @54
    @57
    @0
    cn
    wcel
    cS
    cN
    nnsub
    biimp3a
    nnnn0d
    sylbi
    syl
    @0
    nn0fz0
    sylib
    wph
    vx
    cP
    cQ
    cS
    @0
    cN
    crctcshwlkn0lem.s
    crctcshwlkn0lem.q
    crctcshwlkn0lem2
    mpdan
    wph
    @8
    @7
    cS
    caddc
    co
    cN
    cmin
    co
    #
    cP
    cfv
    #
    @19
    wph
    @7
    @7
    cN
    cfz
    co
    wcel
    #
    @8
    @81
    wceq
    wph
    cN
    @7
    cuz
    cfv
    wcel
    #
    @82
    wph
    @7
    cz
    wcel
    #
    cN
    cz
    wcel
    #
    @7
    cN
    cle
    wbr
    #
    w3a
    #
    @83
    wph
    @55
    @87
    crctcshwlkn0lem.s
    @55
    @84
    @85
    @86
    @55
    @0
    @55
    cN
    cS
    cS
    c1
    cN
    elfzoel2
    #
    cS
    c1
    cN
    elfzoelz
    #
    zsubcld
    peano2zd
    @88
    @55
    @58
    @86
    @59
    @56
    @54
    @86
    @57
    @63
    cN
    cr
    wcel
    #
    @56
    wa
    #
    @86
    @54
    @56
    @91
    @54
    @90
    @56
    cN
    nnre
    anim1i
    ancoms
    cN
    cS
    crctcshwlkn0lem1
    syl
    3adant3
    sylbi
    3jca
    syl
    @7
    cN
    eluz2
    sylibr
    @7
    cN
    eluzfz1
    syl
    wph
    vx
    cP
    cQ
    cS
    @7
    cN
    crctcshwlkn0lem.s
    crctcshwlkn0lem.q
    crctcshwlkn0lem3
    mpdan
    wph
    @80
    c1
    cP
    wph
    @55
    @80
    c1
    wceq
    #
    crctcshwlkn0lem.s
    @55
    @58
    @92
    @59
    @56
    @54
    @92
    @57
    @56
    @66
    @65
    @92
    @54
    @68
    @67
    @66
    @65
    wa
    #
    c1
    @7
    @0
    cmin
    co
    #
    @80
    @93
    @0
    cc
    wcel
    #
    c1
    cc
    wcel
    #
    c1
    @94
    wceq
    @65
    @66
    @95
    cN
    cS
    subcl
    ancoms
    #
    ax-1cn
    @95
    @96
    wa
    @94
    c1
    @0
    c1
    pncan2
    eqcomd
    sylancl
    @93
    @7
    cN
    cS
    @93
    @95
    @7
    cc
    wcel
    @97
    @0
    peano2cn
    syl
    @66
    @65
    simpr
    @66
    @65
    simpl
    subsub3d
    eqtr2d
    syl2an
    3adant3
    sylbi
    syl
    fveq2d
    eqtrd
    wph
    @10
    @0
    cF
    cS
    ccsh
    co
    #
    cfv
    #
    @23
    @0
    cH
    @98
    crctcshwlkn0lem.h
    fveq1i
    wph
    @55
    @99
    @23
    wceq
    #
    crctcshwlkn0lem.s
    wph
    @55
    wa
    #
    cF
    cA
    cword
    wcel
    #
    cS
    cz
    wcel
    #
    @0
    cc0
    @21
    cfzo
    co
    #
    wcel
    @100
    wph
    @102
    @55
    crctcshwlkn0lem.f
    adantr
    @55
    @103
    wph
    @89
    adantl
    @101
    @0
    @52
    @104
    @55
    @0
    @52
    wcel
    #
    wph
    @55
    cS
    c1
    cN
    cfz
    co
    wcel
    @105
    cS
    c1
    cN
    elfzofz
    cS
    cN
    ubmelfzo
    syl
    adantl
    @21
    cN
    cc0
    cfzo
    @71
    oveq2i
    syl6eleqr
    @0
    cS
    cA
    cF
    cshwidxmod
    syl3anc
    mpdan
    syl5eq
    @75
    @76
    @77
    w3a
    #
    @9
    @13
    @15
    @20
    @26
    @28
    @106
    @6
    @18
    @8
    @19
    @75
    @76
    @77
    simp1
    #
    @75
    @76
    @77
    simp2
    #
    eqeq12d
    @106
    @11
    @24
    @12
    @25
    @106
    @10
    @23
    cI
    @75
    @76
    @77
    simp3
    fveq2d
    #
    @106
    @6
    @18
    @107
    sneqd
    eqeq12d
    @106
    @14
    @27
    @11
    @24
    @106
    @6
    @18
    @8
    @19
    @107
    @108
    preq12d
    @109
    sseq12d
    ifpbi123d
    syl3anc
    mpbird
    adantr
    @1
    @5
    @16
    wb
    wph
    cJ
    @0
    cQ
    cH
    cI
    wkslem1
    adantl
    mpbird
end
