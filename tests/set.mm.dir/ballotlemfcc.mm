include "cv.mm"
include "cfv.mm"
include "cc0.mm"
include "wceq.mm"
include "cle.mm"
include "wbr.mm"
include "c1.mm"
include "cfz.mm"
include "co.mm"
include "crab.mm"
include "wrex.mm"
include "wral.mm"
include "wcel.mm"
include "wa.mm"
include "fveq2.mm"
include "breq2d.mm"
include "elrab.mm"
include "anbi1i.mm"
include "cmin.mm"
include "wn.mm"
include "caddc.mm"
include "simprl.mm"
include "adantrr.mm"
include "clt.mm"
include "cr.mm"
include "cz.mm"
include "cuz.mm"
include "fzssuz.mm"
include "uzssz.mm"
include "sstri.mm"
include "zssre.mm"
include "sseli.mm"
include "ltp1d.mm"
include "1red.mm"
include "readdcld.mm"
include "ltnled.mm"
include "mpbid.mm"
include "syl.mm"
include "wi.mm"
include "simprr.mm"
include "adantr.mm"
include "simpr.mm"
include "fveq2d.mm"
include "breq1d.mm"
include "wb.mm"
include "cn.mm"
include "elnnuz.mm"
include "sylib.mm"
include "eluzfz2.mm"
include "eleq1.mm"
include "syl5ibrcom.mm"
include "anc2li.mm"
include "1eluzge0.mm"
include "fzss1.mm"
include "sseld.mm"
include "ax-mp.mm"
include "elfzelz.mm"
include "adantl.mm"
include "ballotlemfelz.mm"
include "zred.mm"
include "0red.mm"
include "sylan2.mm"
include "syl6.mm"
include "imp.mm"
include "bitr3d.mm"
include "ex.mm"
include "con2d.mm"
include "wo.mm"
include "nn1m1nn.mm"
include "csn.mm"
include "oveq1.mm"
include "nnzd.mm"
include "fzsn.mm"
include "eqtr3d.mm"
include "rexeqdv.mm"
include "rexsng.mm"
include "pm2.65da.mm"
include "biortn.mm"
include "notnotb.mm"
include "orbi1i.mm"
include "syl6bbr.mm"
include "mpbird.mm"
include "elfzp1.mm"
include "nncnd.mm"
include "1cnd.mm"
include "npcand.mm"
include "oveq2d.mm"
include "eleq2d.mm"
include "eqeq2d.mm"
include "orbi2d.mm"
include "3bitr3d.mm"
include "orcom.mm"
include "syl6bb.mm"
include "biimpd.mm"
include "pm5.6.mm"
include "sylibr.mm"
include "1z.mm"
include "jctil.mm"
include "jctir.mm"
include "fzaddel.mm"
include "syl2an.mm"
include "biimp3a.mm"
include "3anidm23.mm"
include "c2.mm"
include "1p1e2.mm"
include "a1i.mm"
include "oveq12d.mm"
include "wss.mm"
include "2eluzge1.mm"
include "syl6bi.mm"
include "mpd.mm"
include "syld.mm"
include "sylan2d.mm"
include "breq1.mm"
include "rspccva.mm"
include "sylan2br.mm"
include "expr.mm"
include "con3d.mm"
include "syl2anc.mm"
include "simplrr.mm"
include "simpll.mm"
include "mpsyl.mm"
include "imdistani.mm"
include "elfznn.mm"
include "ballotlemfp1.mm"
include "simprd.mm"
include "sylan.mm"
include "zcnd.mm"
include "pncand.mm"
include "oveq1d.mm"
include "0z.mm"
include "zleltp1.mm"
include "sylancr.mm"
include "breq2.mm"
include "bitr4d.mm"
include "syl21anc.mm"
include "ltled.mm"
include "adantlrr.mm"
include "syl12anc.mm"
include "mtand.mm"
include "simpld.mm"
include "mpdan.mm"
include "notbid.mm"
include "syldan.mm"
include "zlem1lt.mm"
include "mpan2.mm"
include "zre.mm"
include "resubcld.mm"
include "bitrd.mm"
include "simprlr.mm"
include "letri3d.mm"
include "mpbir2and.mm"
include "sylan2b.mm"
include "cfn.mm"
include "c0.mm"
include "wne.mm"
include "ssrab2.mm"
include "fzfi.mm"
include "ssfi.mm"
include "mp2an.mm"
include "rabn0.mm"
include "fimaxre.mm"
include "syl3anc.mm"
include "reximddv.mm"
include "elrabi.mm"
include "anim1i.mm"
include "reximi2.mm"

theorem ballotlemfcc
  let wph: wff ph
  let vx: setvar x
  let cC: class C
  let cP: class P
  let vi: setvar i
  let vk: setvar k
  let cF: class F
  let cJ: class J
  let cM: class M
  let cN: class N
  let cO: class O
  let vc: setvar c
  let vj: setvar j
  assume ballotth.m: |- M e. NN
  assume ballotth.n: |- N e. NN
  assume ballotth.o: |- O = { c e. ~P ( 1 ... ( M + N ) ) | ( # ` c ) = M }
  assume ballotth.p: |- P = ( x e. ~P O |-> ( ( # ` x ) / ( # ` O ) ) )
  assume ballotth.f: |- F = ( c e. O |-> ( i e. ZZ |-> ( ( # ` ( ( 1 ... i ) i^i c ) ) - ( # ` ( ( 1 ... i ) \ c ) ) ) ) )
  assume ballotlemfcc.c: |- ( ph -> C e. O )
  assume ballotlemfcc.j: |- ( ph -> J e. NN )
  assume ballotlemfcc.3: |- ( ph -> E. i e. ( 1 ... J ) 0 <_ ( ( F ` C ) ` i ) )
  assume ballotlemfcc.4: |- ( ph -> ( ( F ` C ) ` J ) < 0 )

  disjoint J i
  disjoint i ph
  disjoint i k
  disjoint J k
  disjoint C k
  disjoint k ph
  disjoint M c
  disjoint N c
  disjoint O c
  disjoint M i
  disjoint N i
  disjoint O i
  disjoint M k
  disjoint N k
  disjoint O k
  disjoint c i
  disjoint F c
  disjoint F i
  disjoint F k
  disjoint C i
  disjoint j k
  disjoint i j
  disjoint J j
  disjoint C j
  disjoint M j
  disjoint N j
  disjoint O j
  disjoint F j
  assert |- ( ph -> E. k e. ( 1 ... J ) ( ( F ` C ) ` k ) = 0 )

  proof
    wph
    vk
    cv
    #
    cC
    cF
    cfv
    #
    cfv
    #
    cc0
    wceq
    #
    vk
    cc0
    vi
    cv
    #
    @1
    cfv
    #
    cle
    wbr
    #
    vi
    c1
    cJ
    cfz
    co
    #
    crab
    #
    wrex
    @3
    vk
    @7
    wrex
    wph
    vj
    cv
    #
    @0
    cle
    wbr
    #
    vj
    @8
    wral
    #
    @3
    vk
    @8
    @0
    @8
    wcel
    #
    @11
    wa
    wph
    @0
    @7
    wcel
    #
    cc0
    @2
    cle
    wbr
    #
    wa
    #
    @11
    wa
    #
    @3
    @12
    @15
    @11
    @6
    @14
    vi
    @0
    @7
    @4
    @0
    wceq
    @5
    @2
    cc0
    cle
    @4
    @0
    @1
    fveq2
    breq2d
    elrab
    anbi1i
    wph
    @16
    wa
    #
    @3
    @2
    cc0
    cle
    wbr
    #
    @14
    @17
    @18
    cc0
    @2
    c1
    cmin
    co
    #
    cle
    wbr
    #
    wn
    #
    @17
    cc0
    @0
    c1
    caddc
    co
    #
    @1
    cfv
    #
    cle
    wbr
    #
    wn
    #
    @21
    @17
    @22
    @0
    cle
    wbr
    #
    wn
    #
    @25
    @17
    @13
    @27
    wph
    @15
    @13
    @11
    wph
    @13
    @14
    simprl
    #
    adantrr
    @13
    @0
    @22
    clt
    wbr
    @27
    @13
    @0
    @7
    cr
    @0
    @7
    cz
    cr
    @7
    c1
    cuz
    cfv
    #
    cz
    c1
    cJ
    fzssuz
    c1
    uzssz
    sstri
    zssre
    sstri
    #
    sseli
    #
    ltp1d
    @13
    @0
    @22
    @31
    @13
    @0
    c1
    @31
    @13
    1red
    readdcld
    ltnled
    mpbid
    syl
    #
    @17
    @11
    @22
    @7
    wcel
    #
    @27
    @25
    wi
    wph
    @15
    @11
    simprr
    wph
    @15
    @33
    @11
    wph
    @15
    @33
    wph
    @14
    @0
    cJ
    wceq
    #
    wn
    #
    @13
    @33
    wph
    @34
    @14
    wph
    @34
    @14
    wn
    #
    wph
    @34
    wa
    #
    cJ
    @1
    cfv
    #
    cc0
    clt
    wbr
    #
    @36
    wph
    @39
    @34
    ballotlemfcc.4
    adantr
    @37
    @2
    cc0
    clt
    wbr
    #
    @39
    @36
    @37
    @2
    @38
    cc0
    clt
    @37
    @0
    cJ
    @1
    wph
    @34
    simpr
    fveq2d
    breq1d
    wph
    @34
    @40
    @36
    wb
    #
    wph
    @34
    wph
    @13
    wa
    @41
    wph
    @34
    @13
    wph
    @13
    @34
    cJ
    @7
    wcel
    #
    wph
    cJ
    @29
    wcel
    #
    @42
    wph
    cJ
    cn
    wcel
    #
    @43
    ballotlemfcc.j
    cJ
    elnnuz
    sylib
    c1
    cJ
    eluzfz2
    syl
    @0
    cJ
    @7
    eleq1
    syl5ibrcom
    anc2li
    @13
    wph
    @0
    cc0
    cJ
    cfz
    co
    #
    wcel
    #
    @41
    c1
    cc0
    cuz
    cfv
    wcel
    #
    @13
    @46
    wi
    1eluzge0
    @47
    @7
    @45
    @0
    c1
    cc0
    cJ
    fzss1
    #
    sseld
    ax-mp
    #
    wph
    @46
    wa
    #
    @2
    cc0
    @50
    @2
    @50
    vx
    cC
    cP
    vi
    cF
    @0
    cM
    cN
    cO
    vc
    ballotth.m
    ballotth.n
    ballotth.o
    ballotth.p
    ballotth.f
    wph
    cC
    cO
    wcel
    #
    @46
    ballotlemfcc.c
    adantr
    @46
    @0
    cz
    wcel
    #
    wph
    @0
    cc0
    cJ
    elfzelz
    adantl
    ballotlemfelz
    #
    zred
    @50
    0red
    ltnled
    sylan2
    syl6
    imp
    bitr3d
    mpbid
    ex
    con2d
    wph
    @13
    @35
    wa
    #
    @0
    c1
    cJ
    c1
    cmin
    co
    #
    cfz
    co
    wcel
    #
    @33
    wph
    @13
    @34
    @56
    wo
    #
    wi
    @54
    @56
    wi
    wph
    @13
    @57
    wph
    @13
    @56
    @34
    wo
    #
    @57
    wph
    @0
    c1
    @55
    c1
    caddc
    co
    #
    cfz
    co
    #
    wcel
    #
    @56
    @0
    @59
    wceq
    #
    wo
    #
    @13
    @58
    wph
    @55
    @29
    wcel
    #
    @61
    @63
    wb
    wph
    @55
    cn
    wcel
    #
    @64
    wph
    @65
    cJ
    c1
    wceq
    #
    @65
    wo
    #
    wph
    @44
    @67
    ballotlemfcc.j
    cJ
    nn1m1nn
    syl
    wph
    @65
    @66
    wn
    #
    wn
    #
    @65
    wo
    #
    @67
    wph
    @68
    @65
    @70
    wb
    wph
    @66
    cc0
    @38
    cle
    wbr
    #
    wph
    @66
    wa
    #
    @6
    vi
    cJ
    csn
    #
    wrex
    #
    @71
    @72
    @6
    vi
    @7
    wrex
    #
    @74
    wph
    @75
    @66
    ballotlemfcc.3
    adantr
    @72
    @6
    vi
    @7
    @73
    @72
    cJ
    cJ
    cfz
    co
    #
    @7
    @73
    @66
    @76
    @7
    wceq
    wph
    cJ
    c1
    cJ
    cfz
    oveq1
    adantl
    wph
    @76
    @73
    wceq
    #
    @66
    wph
    cJ
    cz
    wcel
    @77
    wph
    cJ
    ballotlemfcc.j
    nnzd
    #
    cJ
    fzsn
    syl
    adantr
    eqtr3d
    rexeqdv
    mpbid
    wph
    @74
    @71
    wb
    #
    @66
    wph
    @44
    @79
    ballotlemfcc.j
    @6
    @71
    vi
    cJ
    cn
    @4
    cJ
    wceq
    @5
    @38
    cc0
    cle
    @4
    cJ
    @1
    fveq2
    breq2d
    rexsng
    syl
    adantr
    mpbid
    @72
    @39
    @71
    wn
    #
    wph
    @39
    @66
    ballotlemfcc.4
    adantr
    wph
    @39
    @80
    wb
    @66
    wph
    @38
    cc0
    wph
    @38
    wph
    vx
    cC
    cP
    vi
    cF
    cJ
    cM
    cN
    cO
    vc
    ballotth.m
    ballotth.n
    ballotth.o
    ballotth.p
    ballotth.f
    ballotlemfcc.c
    @78
    ballotlemfelz
    zred
    wph
    0red
    ltnled
    adantr
    mpbid
    pm2.65da
    @68
    @65
    biortn
    syl
    @66
    @69
    @65
    @66
    notnotb
    orbi1i
    syl6bbr
    mpbird
    #
    @55
    elnnuz
    sylib
    @0
    c1
    @55
    elfzp1
    syl
    wph
    @60
    @7
    @0
    wph
    @59
    cJ
    c1
    cfz
    wph
    cJ
    c1
    wph
    cJ
    ballotlemfcc.j
    nncnd
    wph
    1cnd
    npcand
    #
    oveq2d
    eleq2d
    wph
    @62
    @34
    @56
    wph
    @59
    cJ
    @0
    @82
    eqeq2d
    orbi2d
    3bitr3d
    @56
    @34
    orcom
    syl6bb
    biimpd
    @13
    @34
    @56
    pm5.6
    sylibr
    wph
    @56
    @33
    wph
    @56
    wa
    @22
    c1
    c1
    caddc
    co
    #
    @59
    cfz
    co
    #
    wcel
    #
    @33
    wph
    @56
    @85
    wph
    @56
    @56
    @85
    wph
    c1
    cz
    wcel
    #
    @55
    cz
    wcel
    #
    wa
    @52
    @86
    wa
    @56
    @85
    wb
    @56
    wph
    @87
    @86
    wph
    @55
    @81
    nnzd
    1z
    jctil
    @56
    @52
    @86
    @0
    c1
    @55
    elfzelz
    1z
    jctir
    @0
    c1
    c1
    @55
    fzaddel
    syl2an
    biimp3a
    3anidm23
    wph
    @85
    @33
    wi
    @56
    wph
    @85
    @22
    c2
    cJ
    cfz
    co
    #
    wcel
    @33
    wph
    @84
    @88
    @22
    wph
    @83
    c2
    @59
    cJ
    cfz
    @83
    c2
    wceq
    wph
    1p1e2
    a1i
    @82
    oveq12d
    eleq2d
    @88
    @7
    @22
    c2
    @29
    wcel
    @88
    @7
    wss
    2eluzge1
    c2
    c1
    cJ
    fzss1
    ax-mp
    sseli
    syl6bi
    adantr
    mpd
    ex
    syld
    sylan2d
    #
    imp
    #
    adantrr
    #
    @11
    @33
    wa
    @24
    @26
    @11
    @33
    @24
    @26
    @33
    @24
    wa
    @11
    @22
    @8
    wcel
    @26
    @6
    @24
    vi
    @22
    @7
    @4
    @22
    wceq
    @5
    @23
    cc0
    cle
    @4
    @22
    @1
    fveq2
    breq2d
    elrab
    @10
    @26
    vj
    @22
    @8
    @9
    @22
    @0
    cle
    breq1
    rspccva
    sylan2br
    #
    expr
    con3d
    syl2anc
    mpd
    @17
    @23
    @19
    wceq
    #
    @25
    @21
    wb
    @17
    @22
    cC
    wcel
    #
    wn
    #
    @93
    @17
    @94
    @26
    @32
    @17
    @94
    wa
    @11
    @33
    @24
    @26
    wph
    @15
    @11
    @94
    simplrr
    @17
    @33
    @94
    @91
    adantr
    wph
    @15
    @94
    @24
    @11
    wph
    @15
    wa
    #
    @94
    wa
    #
    cc0
    @23
    @97
    0red
    @97
    wph
    @22
    @45
    wcel
    #
    @23
    cr
    wcel
    wph
    @15
    @94
    simpll
    #
    @47
    @97
    @33
    @98
    1eluzge0
    @96
    @33
    @94
    @90
    adantr
    @47
    @7
    @45
    @22
    @48
    sseld
    mpsyl
    wph
    @98
    wa
    #
    @23
    @100
    vx
    cC
    cP
    vi
    cF
    @22
    cM
    cN
    cO
    vc
    ballotth.m
    ballotth.n
    ballotth.o
    ballotth.p
    ballotth.f
    wph
    @51
    @98
    ballotlemfcc.c
    adantr
    @98
    @22
    cz
    wcel
    wph
    @22
    cc0
    cJ
    elfzelz
    adantl
    ballotlemfelz
    zred
    syl2anc
    @97
    @14
    cc0
    @23
    clt
    wbr
    #
    wph
    @13
    @14
    @94
    simplrr
    @97
    wph
    @46
    @23
    @2
    c1
    caddc
    co
    #
    wceq
    #
    @14
    @101
    wb
    @99
    @97
    @13
    @46
    @96
    @13
    @94
    @28
    adantr
    #
    @49
    syl
    @97
    @23
    @22
    c1
    cmin
    co
    #
    @1
    cfv
    #
    c1
    caddc
    co
    #
    wceq
    #
    @103
    @96
    wph
    @33
    wa
    #
    @94
    @108
    wph
    @15
    @33
    @89
    imdistani
    #
    @109
    @94
    @108
    @109
    @95
    @23
    @106
    c1
    cmin
    co
    #
    wceq
    #
    wi
    #
    @94
    @108
    wi
    #
    @109
    vx
    cC
    cP
    vi
    cF
    @22
    cM
    cN
    cO
    vc
    ballotth.m
    ballotth.n
    ballotth.o
    ballotth.p
    ballotth.f
    wph
    @51
    @33
    ballotlemfcc.c
    adantr
    @33
    @22
    cn
    wcel
    wph
    @22
    cJ
    elfznn
    adantl
    ballotlemfp1
    #
    simprd
    imp
    sylan
    @97
    @13
    @108
    @103
    wb
    @104
    @13
    @107
    @102
    @23
    @13
    @106
    @2
    c1
    caddc
    @13
    @105
    @0
    @1
    @13
    @0
    c1
    @13
    @0
    @0
    c1
    cJ
    elfzelz
    zcnd
    @13
    1cnd
    pncand
    fveq2d
    #
    oveq1d
    eqeq2d
    syl
    mpbid
    @50
    @103
    wa
    @14
    cc0
    @102
    clt
    wbr
    #
    @101
    @50
    @14
    @117
    wb
    #
    @103
    @50
    cc0
    cz
    wcel
    #
    @2
    cz
    wcel
    #
    @118
    0z
    @53
    cc0
    @2
    zleltp1
    sylancr
    adantr
    @103
    @101
    @117
    wb
    @50
    @23
    @102
    cc0
    clt
    breq2
    adantl
    bitr4d
    syl21anc
    mpbid
    ltled
    adantlrr
    @92
    syl12anc
    mtand
    wph
    @15
    @95
    @93
    @11
    @96
    @95
    wa
    #
    @112
    @93
    @96
    @109
    @95
    @112
    @110
    @109
    @95
    @112
    @109
    @113
    @114
    @115
    simpld
    imp
    sylan
    @121
    @13
    @112
    @93
    wb
    @96
    @13
    @95
    @28
    adantr
    @13
    @111
    @19
    @23
    @13
    @106
    @2
    c1
    cmin
    @116
    oveq1d
    eqeq2d
    syl
    mpbid
    adantlrr
    mpdan
    @93
    @24
    @20
    @23
    @19
    cc0
    cle
    breq2
    notbid
    syl
    mpbid
    @17
    @120
    @18
    @21
    wb
    wph
    @15
    @120
    @11
    wph
    @15
    @46
    @120
    @96
    @13
    @46
    @28
    @49
    syl
    @53
    syldan
    adantrr
    #
    @120
    @18
    @19
    cc0
    clt
    wbr
    #
    @21
    @120
    @119
    @18
    @123
    wb
    0z
    @2
    cc0
    zlem1lt
    mpan2
    @120
    @19
    cc0
    @120
    @2
    c1
    @2
    zre
    @120
    1red
    resubcld
    @120
    0red
    ltnled
    bitrd
    syl
    mpbird
    wph
    @13
    @14
    @11
    simprlr
    @17
    @2
    cc0
    @17
    @2
    @122
    zred
    @17
    0red
    letri3d
    mpbir2and
    sylan2b
    wph
    @8
    cr
    wss
    #
    @8
    cfn
    wcel
    #
    @8
    c0
    wne
    #
    @11
    vk
    @8
    wrex
    @124
    wph
    @8
    @7
    cr
    @6
    vi
    @7
    ssrab2
    #
    @30
    sstri
    a1i
    @125
    wph
    @7
    cfn
    wcel
    @8
    @7
    wss
    @125
    c1
    cJ
    fzfi
    @127
    @7
    @8
    ssfi
    mp2an
    a1i
    wph
    @75
    @126
    ballotlemfcc.3
    @6
    vi
    @7
    rabn0
    sylibr
    vk
    vj
    @8
    fimaxre
    syl3anc
    reximddv
    @3
    @3
    vk
    @8
    @7
    @12
    @13
    @3
    @6
    vi
    @0
    @7
    elrabi
    anim1i
    reximi2
    syl
end
