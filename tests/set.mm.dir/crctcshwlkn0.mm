include "cc0.mm"
include "wne.mm"
include "wa.mm"
include "cwlks.mm"
include "cfv.mm"
include "wbr.mm"
include "cdm.mm"
include "cword.mm"
include "wcel.mm"
include "chash.mm"
include "cfz.mm"
include "co.mm"
include "wf.mm"
include "cv.mm"
include "c1.mm"
include "caddc.mm"
include "wceq.mm"
include "csn.mm"
include "cpr.mm"
include "wss.mm"
include "wif.mm"
include "cfzo.mm"
include "wral.mm"
include "w3a.mm"
include "ccsh.mm"
include "ccrcts.mm"
include "crctiswlk.mm"
include "wlkf.mm"
include "3syl.mm"
include "cshwcl.mm"
include "syl.mm"
include "syl5eqel.mm"
include "adantr.mm"
include "cmin.mm"
include "cle.mm"
include "cif.mm"
include "wi.mm"
include "wlkp.mm"
include "simpll.mm"
include "cn0.mm"
include "elfznn0.mm"
include "adantl.mm"
include "elfzonn0.mm"
include "nn0addcld.mm"
include "elfz3nn0.mm"
include "syl5eqelr.mm"
include "ad2antlr.mm"
include "cr.mm"
include "wb.mm"
include "elfzelz.mm"
include "zred.mm"
include "elfzoelz.mm"
include "elfzel2.mm"
include "leaddsub.mm"
include "syl3anc.mm"
include "biimpar.mm"
include "syl6breq.mm"
include "3jca.mm"
include "sylanl1.mm"
include "elfz2nn0.mm"
include "sylibr.mm"
include "adantll.mm"
include "ffvelrnd.mm"
include "wn.mm"
include "cz.mm"
include "elfzoel2.mm"
include "zaddcl.mm"
include "adantrr.mm"
include "simprr.mm"
include "zsubcld.mm"
include "clt.mm"
include "zsubcl.mm"
include "ancoms.mm"
include "zre.mm"
include "ltnle.mm"
include "syl2anr.mm"
include "ltsubadd.mm"
include "syl2an23an.mm"
include "posdifd.mm"
include "0red.mm"
include "ltle.mm"
include "syl2anc.mm"
include "sylbid.mm"
include "sylbird.mm"
include "imp.mm"
include "jca.mm"
include "exp31.mm"
include "syl11.mm"
include "imp31.mm"
include "elnn0z.mm"
include "cn.mm"
include "elfzo0.mm"
include "nn0re.mm"
include "3ad2ant1.mm"
include "anim12ci.mm"
include "nnre.mm"
include "3ad2ant2.mm"
include "simpr3.mm"
include "syl2an.mm"
include "3impia.mm"
include "jca32.mm"
include "syl2anb.mm"
include "le2add.mm"
include "ex.mm"
include "lesubadd.mm"
include "mpbird.mm"
include "ifclda.mm"
include "exp32.mm"
include "mpcom.mm"
include "fmptd.mm"
include "crctcshlem2.mm"
include "oveq2d.mm"
include "feq2d.mm"
include "wlkprop.mm"
include "eqcomi.mm"
include "oveq2i.mm"
include "raleqi.mm"
include "fzo1fzo0n0.mm"
include "simplbi2.mm"
include "simplll.mm"
include "wkslem1.mm"
include "cbvralv.mm"
include "biimpi.mm"
include "ctrls.mm"
include "crctprop.mm"
include "fveq2i.mm"
include "eqeq2i.mm"
include "eqcomd.mm"
include "ad2antrl.mm"
include "crctcshwlkn0lem7.mm"
include "raleqdv.mm"
include "syl5bi.mm"
include "com23.mm"
include "cvv.mm"
include "crctcshlem3.mm"
include "iswlk.mm"

theorem crctcshwlkn0
  let wph: wff ph
  let vx: setvar x
  let cP: class P
  let cQ: class Q
  let cS: class S
  let cF: class F
  let cG: class G
  let cH: class H
  let cI: class I
  let cN: class N
  let cV: class V
  let vi: setvar i
  let vj: setvar j
  let vk: setvar k
  assume crctcsh.v: |- V = ( Vtx ` G )
  assume crctcsh.i: |- I = ( iEdg ` G )
  assume crctcsh.d: |- ( ph -> F ( Circuits ` G ) P )
  assume crctcsh.n: |- N = ( # ` F )
  assume crctcsh.s: |- ( ph -> S e. ( 0 ..^ N ) )
  assume crctcsh.h: |- H = ( F cyclShift S )
  assume crctcsh.q: |- Q = ( x e. ( 0 ... N ) |-> if ( x <_ ( N - S ) , ( P ` ( x + S ) ) , ( P ` ( ( x + S ) - N ) ) ) )

  disjoint N x
  disjoint P x
  disjoint S x
  disjoint ph x
  disjoint F x
  disjoint I x
  disjoint V x
  disjoint F i
  disjoint F j
  disjoint F k
  disjoint i j
  disjoint i k
  disjoint i x
  disjoint j k
  disjoint j x
  disjoint k x
  disjoint G i
  disjoint G j
  disjoint H j
  disjoint I i
  disjoint I j
  disjoint I k
  disjoint N i
  disjoint N j
  disjoint N k
  disjoint P i
  disjoint P j
  disjoint P k
  disjoint Q j
  disjoint S i
  disjoint S j
  disjoint S k
  disjoint V i
  disjoint V j
  disjoint V k
  disjoint i ph
  disjoint j ph
  disjoint k ph
  assert |- ( ( ph /\ S =/= 0 ) -> H ( Walks ` G ) Q )

  proof
    wph
    cS
    cc0
    wne
    #
    wa
    #
    cH
    cQ
    cG
    cwlks
    cfv
    #
    wbr
    #
    cH
    cI
    cdm
    #
    cword
    #
    wcel
    #
    cc0
    cH
    chash
    cfv
    #
    cfz
    co
    #
    cV
    cQ
    wf
    #
    vj
    cv
    #
    cQ
    cfv
    #
    @10
    c1
    caddc
    co
    cQ
    cfv
    #
    wceq
    @10
    cH
    cfv
    cI
    cfv
    #
    @11
    csn
    wceq
    @11
    @12
    cpr
    @13
    wss
    wif
    #
    vj
    cc0
    @7
    cfzo
    co
    #
    wral
    #
    w3a
    #
    @1
    @6
    @9
    @16
    wph
    @6
    @0
    wph
    cH
    cF
    cS
    ccsh
    co
    #
    @5
    crctcsh.h
    wph
    cF
    @5
    wcel
    #
    @18
    @5
    wcel
    wph
    cF
    cP
    cG
    ccrcts
    cfv
    wbr
    #
    cF
    cP
    @2
    wbr
    #
    @19
    crctcsh.d
    cP
    cF
    cG
    crctiswlk
    #
    cP
    cF
    cG
    cI
    crctcsh.i
    wlkf
    3syl
    cS
    @4
    cF
    cshwcl
    syl
    syl5eqel
    adantr
    wph
    @9
    @0
    wph
    @9
    cc0
    cN
    cfz
    co
    #
    cV
    cQ
    wf
    wph
    vx
    @23
    vx
    cv
    #
    cN
    cS
    cmin
    co
    #
    cle
    wbr
    #
    @24
    cS
    caddc
    co
    #
    cP
    cfv
    #
    @27
    cN
    cmin
    co
    #
    cP
    cfv
    #
    cif
    #
    cV
    cQ
    wph
    @24
    @23
    wcel
    #
    @31
    cV
    wcel
    #
    @21
    wph
    @32
    @33
    wi
    #
    wph
    @20
    @21
    crctcsh.d
    @22
    syl
    @21
    cc0
    cF
    chash
    cfv
    #
    cfz
    co
    #
    cV
    cP
    wf
    #
    wph
    @34
    wi
    cP
    cF
    cG
    cV
    crctcsh.v
    wlkp
    @37
    wph
    @32
    @33
    @37
    wph
    @32
    wa
    #
    wa
    #
    @26
    @28
    @30
    cV
    @39
    @26
    wa
    @36
    cV
    @27
    cP
    @37
    @38
    @26
    simpll
    @38
    @26
    @27
    @36
    wcel
    #
    @37
    @38
    @26
    wa
    @27
    cn0
    wcel
    #
    @35
    cn0
    wcel
    #
    @27
    @35
    cle
    wbr
    #
    w3a
    #
    @40
    wph
    cS
    cc0
    cN
    cfzo
    co
    #
    wcel
    #
    @32
    @26
    @44
    crctcsh.s
    @46
    @32
    wa
    #
    @26
    wa
    #
    @41
    @42
    @43
    @47
    @41
    @26
    @47
    @24
    cS
    @32
    @24
    cn0
    wcel
    #
    @46
    @24
    cN
    elfznn0
    adantl
    @46
    cS
    cn0
    wcel
    #
    @32
    cS
    cN
    elfzonn0
    adantr
    nn0addcld
    adantr
    @32
    @42
    @46
    @26
    @32
    @35
    cN
    cn0
    crctcsh.n
    @24
    cN
    elfz3nn0
    syl5eqelr
    #
    ad2antlr
    @48
    @27
    cN
    @35
    cle
    @47
    @27
    cN
    cle
    wbr
    #
    @26
    @47
    @24
    cr
    wcel
    #
    cS
    cr
    wcel
    #
    cN
    cr
    wcel
    #
    @52
    @26
    wb
    @32
    @53
    @46
    @32
    @24
    @24
    cc0
    cN
    elfzelz
    #
    zred
    adantl
    @46
    @54
    @32
    @46
    cS
    cS
    cc0
    cN
    elfzoelz
    #
    zred
    adantr
    @32
    @55
    @46
    @32
    cN
    @24
    cc0
    cN
    elfzel2
    zred
    adantl
    @24
    cS
    cN
    leaddsub
    syl3anc
    biimpar
    crctcsh.n
    syl6breq
    3jca
    sylanl1
    @27
    @35
    elfz2nn0
    sylibr
    adantll
    ffvelrnd
    @39
    @26
    wn
    #
    wa
    @36
    cV
    @29
    cP
    @37
    @38
    @58
    simpll
    @38
    @58
    @29
    @36
    wcel
    #
    @37
    @38
    @58
    wa
    @29
    cn0
    wcel
    #
    @42
    @29
    @35
    cle
    wbr
    #
    w3a
    #
    @59
    wph
    @46
    @32
    @58
    @62
    crctcsh.s
    @47
    @58
    wa
    #
    @60
    @42
    @61
    @63
    @29
    cz
    wcel
    #
    cc0
    @29
    cle
    wbr
    #
    wa
    #
    @60
    @46
    @32
    @58
    @66
    @46
    cS
    cz
    wcel
    #
    cN
    cz
    wcel
    #
    @32
    @58
    @66
    wi
    #
    wi
    @57
    cS
    cc0
    cN
    elfzoel2
    #
    @24
    cz
    wcel
    #
    @67
    @68
    wa
    #
    @69
    @32
    @71
    @72
    @58
    @66
    @71
    @72
    wa
    #
    @58
    wa
    @64
    @65
    @73
    @64
    @58
    @73
    @27
    cN
    @71
    @67
    @27
    cz
    wcel
    @68
    @24
    cS
    zaddcl
    adantrr
    #
    @71
    @67
    @68
    simprr
    zsubcld
    #
    adantr
    @73
    @58
    @65
    @73
    @58
    @25
    @24
    clt
    wbr
    #
    @65
    @72
    @25
    cr
    wcel
    @53
    @76
    @58
    wb
    @71
    @72
    @25
    @68
    @67
    @25
    cz
    wcel
    cN
    cS
    zsubcl
    ancoms
    zred
    @24
    zre
    #
    @25
    @24
    ltnle
    syl2anr
    @73
    @76
    cN
    @27
    clt
    wbr
    #
    @65
    @72
    @55
    @54
    @71
    @53
    @76
    @78
    wb
    @68
    @55
    @67
    cN
    zre
    adantl
    #
    @67
    @54
    @68
    cS
    zre
    adantr
    @71
    @53
    @72
    @77
    adantr
    cN
    cS
    @24
    ltsubadd
    syl2an23an
    @73
    @78
    cc0
    @29
    clt
    wbr
    #
    @65
    @73
    cN
    @27
    @72
    @55
    @71
    @79
    adantl
    #
    @73
    @27
    @74
    zred
    #
    posdifd
    @73
    cc0
    cr
    wcel
    @29
    cr
    wcel
    @80
    @65
    wi
    @73
    0red
    @73
    @29
    @75
    zred
    cc0
    @29
    ltle
    syl2anc
    sylbid
    sylbid
    sylbird
    imp
    jca
    exp31
    @56
    syl11
    syl2anc
    imp31
    @29
    elnn0z
    sylibr
    @32
    @42
    @46
    @58
    @51
    ad2antlr
    @63
    @29
    cN
    @35
    cle
    @47
    @29
    cN
    cle
    wbr
    #
    @58
    @47
    @83
    @27
    cN
    cN
    caddc
    co
    cle
    wbr
    #
    @47
    @53
    @54
    wa
    #
    @55
    @55
    wa
    #
    wa
    #
    @24
    cN
    cle
    wbr
    #
    cS
    cN
    cle
    wbr
    #
    wa
    #
    wa
    #
    @84
    @46
    @50
    cN
    cn
    wcel
    #
    cS
    cN
    clt
    wbr
    #
    w3a
    #
    @49
    cN
    cn0
    wcel
    #
    @88
    w3a
    #
    @91
    @32
    cS
    cN
    elfzo0
    @24
    cN
    elfz2nn0
    @94
    @96
    wa
    #
    @87
    @88
    @89
    @97
    @85
    @86
    @94
    @54
    @96
    @53
    @50
    @92
    @54
    @93
    cS
    nn0re
    #
    3ad2ant1
    @49
    @95
    @53
    @88
    @24
    nn0re
    3ad2ant1
    anim12ci
    @94
    @86
    @96
    @92
    @50
    @86
    @93
    @92
    @55
    @55
    cN
    nnre
    #
    @99
    jca
    3ad2ant2
    adantr
    jca
    @94
    @49
    @95
    @88
    simpr3
    @94
    @89
    @96
    @50
    @92
    @93
    @89
    @50
    @54
    @55
    @93
    @89
    wi
    @92
    @98
    @99
    cS
    cN
    ltle
    syl2an
    3impia
    adantr
    jca32
    syl2anb
    @87
    @90
    @84
    @24
    cS
    cN
    cN
    le2add
    imp
    syl
    @47
    @27
    cr
    wcel
    #
    @55
    @55
    w3a
    #
    @83
    @84
    wb
    @46
    @32
    @101
    @46
    @67
    @68
    @32
    @101
    wi
    @57
    @70
    @71
    @72
    @101
    @32
    @71
    @72
    @101
    @73
    @100
    @55
    @55
    @82
    @81
    @81
    3jca
    ex
    @56
    syl11
    syl2anc
    imp
    @27
    cN
    cN
    lesubadd
    syl
    mpbird
    adantr
    crctcsh.n
    syl6breq
    3jca
    sylanl1
    @29
    @35
    elfz2nn0
    sylibr
    adantll
    ffvelrnd
    ifclda
    exp32
    syl
    mpcom
    imp
    crctcsh.q
    fmptd
    wph
    @8
    @23
    cV
    cQ
    wph
    @7
    cN
    cc0
    cfz
    wph
    cP
    cS
    cF
    cG
    cH
    cI
    cN
    cV
    crctcsh.v
    crctcsh.i
    crctcsh.d
    crctcsh.n
    crctcsh.s
    crctcsh.h
    crctcshlem2
    #
    oveq2d
    feq2d
    mpbird
    adantr
    @19
    @37
    vi
    cv
    #
    cP
    cfv
    #
    @103
    c1
    caddc
    co
    cP
    cfv
    #
    wceq
    @103
    cF
    cfv
    cI
    cfv
    #
    @104
    csn
    wceq
    @104
    @105
    cpr
    @106
    wss
    wif
    #
    vi
    cc0
    @35
    cfzo
    co
    #
    wral
    #
    w3a
    #
    @1
    @16
    wph
    @110
    @0
    wph
    @20
    @21
    @110
    crctcsh.d
    @22
    cP
    vi
    cF
    cG
    cI
    cV
    crctcsh.v
    crctcsh.i
    wlkprop
    3syl
    adantr
    @19
    @37
    @109
    @1
    @16
    wi
    @19
    @37
    wa
    #
    @1
    @109
    @16
    @111
    @1
    @109
    @16
    wi
    @109
    @107
    vi
    @45
    wral
    #
    @111
    @1
    wa
    #
    @16
    @107
    vi
    @108
    @45
    @35
    cN
    cc0
    cfzo
    cN
    @35
    crctcsh.n
    eqcomi
    #
    oveq2i
    raleqi
    @113
    @112
    @16
    @113
    @112
    wa
    #
    @16
    @14
    vj
    @45
    wral
    #
    @115
    vx
    @4
    cP
    cQ
    cS
    vk
    vj
    cF
    cH
    cI
    cN
    @1
    cS
    c1
    cN
    cfzo
    co
    wcel
    #
    @111
    @112
    wph
    @0
    @117
    wph
    @46
    @0
    @117
    wi
    crctcsh.s
    @117
    @46
    @0
    cS
    cN
    fzo1fzo0n0
    simplbi2
    syl
    imp
    ad2antlr
    crctcsh.q
    crctcsh.h
    crctcsh.n
    @19
    @37
    @1
    @112
    simplll
    @112
    vk
    cv
    #
    cP
    cfv
    #
    @118
    c1
    caddc
    co
    cP
    cfv
    #
    wceq
    @118
    cF
    cfv
    cI
    cfv
    #
    @119
    csn
    wceq
    @119
    @120
    cpr
    @121
    wss
    wif
    #
    vk
    @45
    wral
    #
    @113
    @112
    @123
    @107
    @122
    vi
    vk
    @45
    @103
    @118
    cP
    cF
    cI
    wkslem1
    cbvralv
    biimpi
    adantl
    @113
    cN
    cP
    cfv
    #
    cc0
    cP
    cfv
    #
    wceq
    #
    @112
    wph
    @126
    @111
    @0
    wph
    @20
    cF
    cP
    cG
    ctrls
    cfv
    wbr
    #
    @125
    @35
    cP
    cfv
    #
    wceq
    #
    wa
    @126
    crctcsh.d
    cP
    cF
    cG
    crctprop
    @129
    @126
    @127
    @129
    @125
    @124
    @129
    @125
    @124
    wceq
    @128
    @124
    @125
    @35
    cN
    cP
    @114
    fveq2i
    eqeq2i
    biimpi
    eqcomd
    adantl
    3syl
    ad2antrl
    adantr
    crctcshwlkn0lem7
    @113
    @16
    @116
    wb
    #
    @112
    wph
    @130
    @111
    @0
    wph
    @14
    vj
    @15
    @45
    wph
    @7
    cN
    cc0
    cfzo
    @102
    oveq2d
    raleqdv
    ad2antrl
    adantr
    mpbird
    ex
    syl5bi
    ex
    com23
    3impia
    mpcom
    3jca
    @1
    cG
    cvv
    wcel
    cH
    cvv
    wcel
    cQ
    cvv
    wcel
    w3a
    #
    @3
    @17
    wb
    wph
    @131
    @0
    wph
    vx
    cP
    cQ
    cS
    cF
    cG
    cH
    cI
    cN
    cV
    crctcsh.v
    crctcsh.i
    crctcsh.d
    crctcsh.n
    crctcsh.s
    crctcsh.h
    crctcsh.q
    crctcshlem3
    adantr
    cQ
    cvv
    vj
    cH
    cG
    cI
    cV
    cvv
    cvv
    crctcsh.v
    crctcsh.i
    iswlk
    syl
    mpbird
end
