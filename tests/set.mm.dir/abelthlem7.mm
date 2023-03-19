include "cfv.mm"
include "cabs.mm"
include "c1.mm"
include "cmin.mm"
include "co.mm"
include "cc0.mm"
include "cfz.mm"
include "cv.mm"
include "caddc.mm"
include "cseq.mm"
include "cexp.mm"
include "cmul.mm"
include "csu.mm"
include "cuz.mm"
include "cc.mm"
include "abelthlem4.mm"
include "csn.mm"
include "eldifad.mm"
include "ffvelrnd.mm"
include "abscld.mm"
include "wcel.mm"
include "ax-1cn.mm"
include "cle.mm"
include "wbr.mm"
include "abelthlem7a.mm"
include "simpld.mm"
include "subcl.mm"
include "sylancr.mm"
include "fzfid.mm"
include "cn0.mm"
include "elfznn0.mm"
include "wa.mm"
include "nn0uz.mm"
include "0zd.mm"
include "ffvelrnda.mm"
include "serf.mm"
include "expcl.mm"
include "sylan.mm"
include "mulcld.mm"
include "sylan2.mm"
include "fsumcl.mm"
include "cmpt.mm"
include "eqid.mm"
include "nn0zd.mm"
include "wceq.mm"
include "eluznn0.mm"
include "fveq2.mm"
include "oveq2.mm"
include "oveq12d.mm"
include "ovex.mm"
include "fvmpt.mm"
include "syl.mm"
include "syldan.mm"
include "cli.mm"
include "cdm.mm"
include "ccom.mm"
include "cbl.mm"
include "cdif.mm"
include "wss.mm"
include "abelthlem2.mm"
include "simprd.mm"
include "sseldd.mm"
include "abelthlem5.mm"
include "mpdan.mm"
include "adantl.mm"
include "eqeltrd.mm"
include "iserex.mm"
include "mpbid.mm"
include "isumcl.mm"
include "readdcld.mm"
include "cr.mm"
include "peano2re.mm"
include "rpred.mm"
include "remulcld.mm"
include "abelthlem6.mm"
include "isumsplit.mm"
include "oveq2d.mm"
include "adddid.mm"
include "3eqtrd.mm"
include "fveq2d.mm"
include "abstrid.mm"
include "eqbrtrd.mm"
include "clt.mm"
include "fsumrecl.mm"
include "absmuld.mm"
include "absge0d.mm"
include "fsumabs.mm"
include "reexpcl.mm"
include "1red.mm"
include "adantr.mm"
include "0cn.mm"
include "cnmetdval.mm"
include "sylancl.mm"
include "subid1d.mm"
include "eqtrd.mm"
include "wb.mm"
include "cxmt.mm"
include "cxr.mm"
include "cnxmet.mm"
include "crp.mm"
include "1rp.mm"
include "rpxr.mm"
include "ax-mp.mm"
include "elbl3.mm"
include "mpanl12.mm"
include "eqbrtrrd.mm"
include "wi.mm"
include "1re.mm"
include "ltle.mm"
include "mpd.mm"
include "simpr.mm"
include "exple1.mm"
include "syl31anc.mm"
include "lemul2ad.mm"
include "absexp.mm"
include "eqtr2d.mm"
include "recnd.mm"
include "mulid1d.mm"
include "3brtr3d.mm"
include "fsumle.mm"
include "letrd.mm"
include "ltp1d.mm"
include "lelttrd.mm"
include "ltled.mm"
include "cdiv.mm"
include "0red.mm"
include "fsumge0.mm"
include "ltmuldiv.mm"
include "syl112anc.mm"
include "mpbird.mm"
include "fvex.mm"
include "cz.mm"
include "uzid.mm"
include "absidm.mm"
include "geolim2.mm"
include "seqex.mm"
include "breldm.mm"
include "expge0d.mm"
include "wral.mm"
include "breq1d.mm"
include "rspccva.mm"
include "lemul1ad.mm"
include "3brtr4d.mm"
include "cvgcmpce.mm"
include "isumrecl.mm"
include "wne.mm"
include "eldifsni.mm"
include "necomd.mm"
include "subeq0.mm"
include "necon3bid.mm"
include "absrpcld.mm"
include "rerpdivcld.mm"
include "isumclim2.mm"
include "eqtr4d.mm"
include "iserabs.mm"
include "reexpcld.mm"
include "difrp.mm"
include "rpcnd.mm"
include "isermulc2.mm"
include "isumle.mm"
include "isumclim.mm"
include "breqtrd.mm"
include "rpdivcld.mm"
include "rpne0d.mm"
include "div12d.mm"
include "rpge0d.mm"
include "mulid2d.mm"
include "resubcl.mm"
include "lemul2d.mm"
include "mul12d.mm"
include "mulcomd.mm"
include "lemuldivd.mm"
include "divassd.mm"
include "posdif.mm"
include "ledivmul.mm"
include "lemuldiv2d.mm"
include "ltleaddd.mm"
include "1cnd.mm"
include "adddird.mm"
include "addcomd.mm"
include "breqtrrd.mm"

theorem abelthlem7
  let wph: wff ph
  let vx: setvar x
  let vz: setvar z
  let cA: class A
  let cR: class R
  let cS: class S
  let vk: setvar k
  let vn: setvar n
  let cF: class F
  let cM: class M
  let cN: class N
  let cX: class X
  let vi: setvar i
  let vj: setvar j
  let vm: setvar m
  let vw: setvar w
  let vy: setvar y
  let vr: setvar r
  let vt: setvar t
  let vv: setvar v
  assume abelth.1: |- ( ph -> A : NN0 --> CC )
  assume abelth.2: |- ( ph -> seq 0 ( + , A ) e. dom ~~> )
  assume abelth.3: |- ( ph -> M e. RR )
  assume abelth.4: |- ( ph -> 0 <_ M )
  assume abelth.5: |- S = { z e. CC | ( abs ` ( 1 - z ) ) <_ ( M x. ( 1 - ( abs ` z ) ) ) }
  assume abelth.6: |- F = ( x e. S |-> sum_ n e. NN0 ( ( A ` n ) x. ( x ^ n ) ) )
  assume abelth.7: |- ( ph -> seq 0 ( + , A ) ~~> 0 )
  assume abelthlem6.1: |- ( ph -> X e. ( S \ { 1 } ) )
  assume abelthlem7.2: |- ( ph -> R e. RR+ )
  assume abelthlem7.3: |- ( ph -> N e. NN0 )
  assume abelthlem7.4: |- ( ph -> A. k e. ( ZZ>= ` N ) ( abs ` ( seq 0 ( + , A ) ` k ) ) < R )
  assume abelthlem7.5: |- ( ph -> ( abs ` ( 1 - X ) ) < ( R / ( sum_ n e. ( 0 ... ( N - 1 ) ) ( abs ` ( seq 0 ( + , A ) ` n ) ) + 1 ) ) )

  disjoint k n
  disjoint k x
  disjoint k z
  disjoint M k
  disjoint n x
  disjoint n z
  disjoint M n
  disjoint x z
  disjoint M x
  disjoint M z
  disjoint R k
  disjoint R n
  disjoint R x
  disjoint R z
  disjoint X k
  disjoint X n
  disjoint X x
  disjoint X z
  disjoint A k
  disjoint A n
  disjoint A x
  disjoint A z
  disjoint N k
  disjoint N n
  disjoint k ph
  disjoint n ph
  disjoint ph x
  disjoint S k
  disjoint S n
  disjoint S x
  disjoint i j
  disjoint i k
  disjoint i m
  disjoint i n
  disjoint i w
  disjoint i x
  disjoint i y
  disjoint i z
  disjoint M i
  disjoint j k
  disjoint j m
  disjoint j n
  disjoint j w
  disjoint j x
  disjoint j y
  disjoint j z
  disjoint M j
  disjoint k m
  disjoint k w
  disjoint k y
  disjoint m n
  disjoint m w
  disjoint m x
  disjoint m y
  disjoint m z
  disjoint M m
  disjoint n w
  disjoint n y
  disjoint w x
  disjoint w y
  disjoint w z
  disjoint M w
  disjoint x y
  disjoint y z
  disjoint M y
  disjoint R i
  disjoint R j
  disjoint R m
  disjoint R w
  disjoint R y
  disjoint i r
  disjoint X i
  disjoint j r
  disjoint X j
  disjoint k r
  disjoint n r
  disjoint r x
  disjoint r z
  disjoint X r
  disjoint i t
  disjoint i v
  disjoint A i
  disjoint j t
  disjoint j v
  disjoint A j
  disjoint k t
  disjoint k v
  disjoint m r
  disjoint m t
  disjoint m v
  disjoint A m
  disjoint n t
  disjoint n v
  disjoint r t
  disjoint r v
  disjoint r w
  disjoint r y
  disjoint A r
  disjoint t v
  disjoint t w
  disjoint t x
  disjoint t y
  disjoint t z
  disjoint A t
  disjoint v w
  disjoint v x
  disjoint v y
  disjoint v z
  disjoint A v
  disjoint A w
  disjoint A y
  disjoint i ph
  disjoint j ph
  disjoint m ph
  disjoint ph r
  disjoint ph v
  disjoint ph w
  disjoint ph y
  disjoint F i
  disjoint F j
  disjoint F r
  disjoint F w
  disjoint F y
  disjoint S i
  disjoint S j
  disjoint S m
  disjoint S r
  disjoint S w
  disjoint S y
  assert |- ( ph -> ( abs ` ( F ` X ) ) < ( ( M + 1 ) x. R ) )

  proof
    wph
    cX
    cF
    cfv
    #
    cabs
    cfv
    #
    c1
    cX
    cmin
    co
    #
    cc0
    cN
    c1
    cmin
    co
    #
    cfz
    co
    #
    vn
    cv
    #
    caddc
    cA
    cc0
    cseq
    #
    cfv
    #
    cX
    @5
    cexp
    co
    #
    cmul
    co
    #
    vn
    csu
    #
    cmul
    co
    #
    cabs
    cfv
    #
    @2
    cN
    cuz
    cfv
    #
    @9
    vn
    csu
    #
    cmul
    co
    #
    cabs
    cfv
    #
    caddc
    co
    #
    cM
    c1
    caddc
    co
    #
    cR
    cmul
    co
    #
    wph
    @0
    wph
    cS
    cc
    cX
    cF
    wph
    vx
    vz
    cA
    cS
    vn
    cF
    cM
    abelth.1
    abelth.2
    abelth.3
    abelth.4
    abelth.5
    abelth.6
    abelthlem4
    wph
    cX
    cS
    c1
    csn
    #
    abelthlem6.1
    eldifad
    ffvelrnd
    abscld
    wph
    @12
    @16
    wph
    @11
    wph
    @2
    @10
    wph
    c1
    cc
    wcel
    #
    cX
    cc
    wcel
    #
    @2
    cc
    wcel
    ax-1cn
    wph
    @22
    @2
    cabs
    cfv
    #
    cM
    c1
    cX
    cabs
    cfv
    #
    cmin
    co
    #
    cmul
    co
    #
    cle
    wbr
    #
    wph
    vx
    vz
    cA
    cS
    vn
    cF
    cM
    cX
    abelth.1
    abelth.2
    abelth.3
    abelth.4
    abelth.5
    abelth.6
    abelth.7
    abelthlem6.1
    abelthlem7a
    #
    simpld
    #
    c1
    cX
    subcl
    sylancr
    #
    wph
    @4
    @9
    vn
    wph
    cc0
    @3
    fzfid
    #
    @5
    @4
    wcel
    #
    wph
    @5
    cn0
    wcel
    #
    @9
    cc
    wcel
    #
    @5
    @3
    elfznn0
    #
    wph
    @33
    wa
    #
    @7
    @8
    wph
    cn0
    cc
    @5
    @6
    wph
    vn
    cA
    cc0
    cn0
    nn0uz
    wph
    0zd
    wph
    cn0
    cc
    @5
    cA
    abelth.1
    ffvelrnda
    serf
    ffvelrnda
    #
    wph
    @22
    @33
    @8
    cc
    wcel
    @29
    cX
    @5
    expcl
    sylan
    #
    mulcld
    #
    sylan2
    #
    fsumcl
    #
    mulcld
    #
    abscld
    #
    wph
    @15
    wph
    @2
    @14
    @30
    wph
    @9
    vn
    vk
    cn0
    vk
    cv
    #
    @6
    cfv
    #
    cX
    @44
    cexp
    co
    #
    cmul
    co
    #
    cmpt
    #
    cN
    @13
    @13
    eqid
    #
    wph
    cN
    abelthlem7.3
    nn0zd
    #
    wph
    @5
    @13
    wcel
    #
    wa
    #
    @33
    @5
    @48
    cfv
    #
    @9
    wceq
    #
    wph
    cN
    cn0
    wcel
    #
    @51
    @33
    abelthlem7.3
    @5
    cN
    eluznn0
    sylan
    #
    vk
    @5
    @47
    @9
    cn0
    @48
    @44
    @5
    wceq
    #
    @45
    @7
    @46
    @8
    cmul
    @44
    @5
    @6
    fveq2
    #
    @44
    @5
    cX
    cexp
    oveq2
    oveq12d
    #
    @48
    eqid
    @7
    @8
    cmul
    ovex
    fvmpt
    #
    syl
    #
    wph
    @51
    @33
    @34
    @56
    @39
    syldan
    #
    wph
    caddc
    @48
    cc0
    cseq
    cli
    cdm
    #
    wcel
    #
    caddc
    @48
    cN
    cseq
    @63
    wcel
    wph
    cX
    cc0
    c1
    cabs
    cmin
    ccom
    #
    cbl
    cfv
    co
    #
    wcel
    #
    @64
    wph
    cS
    @20
    cdif
    #
    @66
    cX
    wph
    c1
    cS
    wcel
    @68
    @66
    wss
    wph
    vz
    cA
    cS
    cM
    abelth.1
    abelth.2
    abelth.3
    abelth.4
    abelth.5
    abelthlem2
    simprd
    abelthlem6.1
    sseldd
    #
    wph
    vx
    vz
    cA
    cS
    vk
    vn
    cF
    cM
    cX
    abelth.1
    abelth.2
    abelth.3
    abelth.4
    abelth.5
    abelth.6
    abelth.7
    abelthlem5
    mpdan
    #
    wph
    vn
    @48
    cc0
    cN
    cn0
    nn0uz
    abelthlem7.3
    @36
    @53
    @9
    cc
    @33
    @54
    wph
    @60
    adantl
    #
    @39
    eqeltrd
    #
    iserex
    mpbid
    #
    isumcl
    #
    mulcld
    #
    abscld
    #
    readdcld
    wph
    @18
    cR
    wph
    cM
    cr
    wcel
    @18
    cr
    wcel
    abelth.3
    cM
    peano2re
    syl
    wph
    cR
    abelthlem7.2
    rpred
    #
    remulcld
    wph
    @1
    @11
    @15
    caddc
    co
    #
    cabs
    cfv
    @17
    cle
    wph
    @0
    @78
    cabs
    wph
    @0
    @2
    cn0
    @9
    vn
    csu
    #
    cmul
    co
    @2
    @10
    @14
    caddc
    co
    #
    cmul
    co
    @78
    wph
    vx
    vz
    cA
    cS
    vn
    cF
    cM
    cX
    abelth.1
    abelth.2
    abelth.3
    abelth.4
    abelth.5
    abelth.6
    abelth.7
    abelthlem6.1
    abelthlem6
    wph
    @79
    @80
    @2
    cmul
    wph
    @9
    vn
    @48
    cc0
    cN
    @13
    cn0
    nn0uz
    @49
    abelthlem7.3
    @71
    @39
    @70
    isumsplit
    oveq2d
    wph
    @2
    @10
    @14
    @30
    @41
    @74
    adddid
    3eqtrd
    fveq2d
    wph
    @11
    @15
    @42
    @75
    abstrid
    eqbrtrd
    wph
    @17
    cR
    cM
    cR
    cmul
    co
    #
    caddc
    co
    #
    @19
    clt
    wph
    @12
    @16
    cR
    @81
    @43
    @76
    @77
    wph
    cM
    cR
    abelth.3
    @77
    remulcld
    #
    wph
    @12
    @23
    @4
    @7
    cabs
    cfv
    #
    vn
    csu
    #
    c1
    caddc
    co
    #
    cmul
    co
    #
    cR
    @43
    wph
    @23
    @86
    wph
    @2
    @30
    abscld
    #
    wph
    @85
    cr
    wcel
    @86
    cr
    wcel
    #
    wph
    @4
    @84
    vn
    @31
    @32
    wph
    @33
    @84
    cr
    wcel
    #
    @35
    @36
    @7
    @37
    abscld
    #
    sylan2
    #
    fsumrecl
    #
    @85
    peano2re
    syl
    #
    remulcld
    @77
    wph
    @12
    @23
    @10
    cabs
    cfv
    #
    cmul
    co
    @87
    cle
    wph
    @2
    @10
    @30
    @41
    absmuld
    wph
    @95
    @86
    @23
    wph
    @10
    @41
    abscld
    #
    @94
    @88
    wph
    @2
    @30
    absge0d
    wph
    @95
    @86
    @96
    @94
    wph
    @95
    @85
    @86
    @96
    @93
    @94
    wph
    @95
    @4
    @9
    cabs
    cfv
    #
    vn
    csu
    @85
    @96
    wph
    @4
    @97
    vn
    @31
    @32
    wph
    @33
    @97
    cr
    wcel
    @35
    @36
    @9
    @39
    abscld
    sylan2
    #
    fsumrecl
    @93
    wph
    @4
    @9
    vn
    @31
    @40
    fsumabs
    wph
    @4
    @97
    @84
    vn
    @31
    @98
    @92
    @32
    wph
    @33
    @97
    @84
    cle
    wbr
    @35
    @36
    @84
    @24
    @5
    cexp
    co
    #
    cmul
    co
    #
    @84
    c1
    cmul
    co
    @97
    @84
    cle
    @36
    @99
    c1
    @84
    wph
    @24
    cr
    wcel
    #
    @33
    @99
    cr
    wcel
    #
    wph
    cX
    @29
    abscld
    #
    @24
    @5
    reexpcl
    sylan
    #
    @36
    1red
    @91
    @36
    @7
    @37
    absge0d
    #
    @36
    @101
    cc0
    @24
    cle
    wbr
    #
    @24
    c1
    cle
    wbr
    #
    @33
    @99
    c1
    cle
    wbr
    wph
    @101
    @33
    @103
    adantr
    wph
    @106
    @33
    wph
    cX
    @29
    absge0d
    #
    adantr
    wph
    @107
    @33
    wph
    @24
    c1
    clt
    wbr
    #
    @107
    wph
    cX
    cc0
    @65
    co
    #
    @24
    c1
    clt
    wph
    @110
    cX
    cc0
    cmin
    co
    #
    cabs
    cfv
    #
    @24
    wph
    @22
    cc0
    cc
    wcel
    #
    @110
    @112
    wceq
    @29
    0cn
    cX
    cc0
    @65
    @65
    eqid
    cnmetdval
    sylancl
    wph
    @111
    cX
    cabs
    wph
    cX
    @29
    subid1d
    fveq2d
    eqtrd
    wph
    @67
    @110
    c1
    clt
    wbr
    #
    @69
    wph
    @113
    @22
    @67
    @114
    wb
    #
    0cn
    @29
    @65
    cc
    cxmt
    cfv
    wcel
    c1
    cxr
    wcel
    #
    @113
    @22
    wa
    @115
    cnxmet
    c1
    crp
    wcel
    @116
    1rp
    c1
    rpxr
    ax-mp
    cX
    @65
    cc0
    c1
    cc
    elbl3
    mpanl12
    sylancr
    mpbid
    eqbrtrrd
    #
    wph
    @101
    c1
    cr
    wcel
    #
    @109
    @107
    wi
    @103
    1re
    @24
    c1
    ltle
    sylancl
    mpd
    #
    adantr
    wph
    @33
    simpr
    @24
    @5
    exple1
    syl31anc
    lemul2ad
    @36
    @97
    @84
    @8
    cabs
    cfv
    #
    cmul
    co
    #
    @100
    @36
    @7
    @8
    @37
    @38
    absmuld
    #
    @36
    @120
    @99
    @84
    cmul
    wph
    @22
    @33
    @120
    @99
    wceq
    @29
    cX
    @5
    absexp
    sylan
    oveq2d
    #
    eqtr2d
    @36
    @84
    @36
    @84
    @91
    recnd
    mulid1d
    3brtr3d
    sylan2
    fsumle
    letrd
    wph
    @85
    @93
    ltp1d
    #
    lelttrd
    ltled
    lemul2ad
    eqbrtrd
    wph
    @87
    cR
    clt
    wbr
    #
    @23
    cR
    @86
    cdiv
    co
    clt
    wbr
    #
    abelthlem7.5
    wph
    @23
    cr
    wcel
    cR
    cr
    wcel
    #
    @89
    cc0
    @86
    clt
    wbr
    @125
    @126
    wb
    @88
    @77
    @94
    wph
    cc0
    @85
    @86
    wph
    0red
    @93
    @94
    wph
    @4
    @84
    vn
    @31
    @92
    @32
    wph
    @33
    cc0
    @84
    cle
    wbr
    @35
    @105
    sylan2
    fsumge0
    @124
    lelttrd
    @23
    cR
    @86
    ltmuldiv
    syl112anc
    mpbird
    lelttrd
    wph
    @16
    @23
    @14
    cabs
    cfv
    #
    cmul
    co
    #
    @81
    cle
    wph
    @2
    @14
    @30
    @74
    absmuld
    wph
    @129
    @81
    cle
    wbr
    @128
    @81
    @23
    cdiv
    co
    #
    cle
    wbr
    wph
    @128
    @13
    @97
    vn
    csu
    #
    @130
    wph
    @14
    @74
    abscld
    #
    wph
    @97
    vn
    vk
    cn0
    @47
    cabs
    cfv
    #
    cmpt
    #
    cN
    @13
    @49
    @50
    @52
    @33
    @5
    @134
    cfv
    #
    @97
    wceq
    @56
    vk
    @5
    @133
    @97
    cn0
    @134
    @57
    @47
    @9
    cabs
    @59
    fveq2d
    @134
    eqid
    @9
    cabs
    fvex
    fvmpt
    syl
    #
    @52
    @9
    @62
    abscld
    #
    wph
    cR
    vn
    vk
    cn0
    @24
    @44
    cexp
    co
    #
    cmpt
    #
    @134
    cN
    cN
    @13
    @49
    wph
    cN
    cz
    wcel
    cN
    @13
    wcel
    @50
    cN
    uzid
    syl
    @52
    @5
    @139
    cfv
    #
    @99
    cr
    @52
    @33
    @140
    @99
    wceq
    @56
    vk
    @5
    @138
    @99
    cn0
    @139
    @44
    @5
    @24
    cexp
    oveq2
    #
    @139
    eqid
    @24
    @5
    cexp
    ovex
    fvmpt
    syl
    #
    wph
    @51
    @33
    @102
    @56
    @104
    syldan
    #
    eqeltrd
    #
    @52
    @135
    @97
    cc
    @136
    @52
    @97
    @137
    recnd
    #
    eqeltrd
    wph
    caddc
    @139
    cN
    cseq
    #
    @24
    cN
    cexp
    co
    #
    @25
    cdiv
    co
    #
    cli
    wbr
    @146
    @63
    wcel
    wph
    @24
    vn
    @139
    cN
    wph
    @24
    @103
    recnd
    wph
    @24
    cabs
    cfv
    #
    @24
    c1
    clt
    wph
    @22
    @149
    @24
    wceq
    @29
    cX
    absidm
    syl
    @117
    eqbrtrd
    abelthlem7.3
    @142
    geolim2
    #
    @146
    @148
    cli
    caddc
    @139
    cN
    seqex
    @147
    @25
    cdiv
    ovex
    breldm
    syl
    @77
    @52
    @97
    cR
    @99
    cmul
    co
    #
    @135
    cabs
    cfv
    #
    cR
    @140
    cmul
    co
    #
    cle
    @52
    @97
    @100
    @151
    cle
    wph
    @51
    @33
    @97
    @100
    wceq
    @56
    @36
    @97
    @121
    @100
    @122
    @123
    eqtrd
    syldan
    @52
    @84
    cR
    @99
    wph
    @51
    @33
    @90
    @56
    @91
    syldan
    #
    wph
    @127
    @51
    @77
    adantr
    #
    @143
    @52
    @24
    @5
    wph
    @101
    @51
    @103
    adantr
    @56
    wph
    @106
    @51
    @108
    adantr
    expge0d
    @52
    @84
    cR
    @154
    @155
    wph
    @45
    cabs
    cfv
    #
    cR
    clt
    wbr
    #
    vk
    @13
    wral
    @51
    @84
    cR
    clt
    wbr
    #
    abelthlem7.4
    @157
    @158
    vk
    @5
    @13
    @57
    @156
    @84
    cR
    clt
    @57
    @45
    @7
    cabs
    @58
    fveq2d
    breq1d
    rspccva
    sylan
    ltled
    lemul1ad
    eqbrtrd
    #
    @52
    @152
    @97
    cabs
    cfv
    #
    @97
    @52
    @135
    @97
    cabs
    @136
    fveq2d
    @52
    @34
    @160
    @97
    wceq
    @62
    @9
    absidm
    syl
    eqtrd
    @52
    @140
    @99
    cR
    cmul
    @142
    oveq2d
    #
    3brtr4d
    cvgcmpce
    #
    isumrecl
    #
    wph
    @81
    @23
    @83
    wph
    @2
    @30
    wph
    @2
    cc0
    wne
    #
    c1
    cX
    wne
    #
    wph
    cX
    c1
    wph
    cX
    @68
    wcel
    cX
    c1
    wne
    abelthlem6.1
    cX
    cS
    c1
    eldifsni
    syl
    necomd
    wph
    @21
    @22
    @164
    @165
    wb
    ax-1cn
    @29
    @21
    @22
    wa
    @2
    cc0
    c1
    cX
    c1
    cX
    subeq0
    necon3bid
    sylancr
    mpbird
    absrpcld
    #
    rerpdivcld
    #
    wph
    @14
    @131
    vn
    @48
    @134
    cN
    @13
    @49
    wph
    @9
    vn
    @48
    cN
    @13
    @49
    @50
    @61
    @62
    @73
    isumclim2
    wph
    @97
    vn
    @134
    cN
    @13
    @49
    @50
    @136
    @145
    @162
    isumclim2
    @50
    wph
    @51
    @33
    @53
    cc
    wcel
    @56
    @72
    syldan
    @52
    @135
    @97
    @53
    cabs
    cfv
    @136
    @52
    @53
    @9
    cabs
    @61
    fveq2d
    eqtr4d
    iserabs
    wph
    @131
    cR
    @148
    cmul
    co
    #
    @130
    @163
    wph
    cR
    @148
    @77
    wph
    @147
    @25
    wph
    @24
    cN
    @103
    abelthlem7.3
    reexpcld
    #
    wph
    @109
    @25
    crp
    wcel
    #
    @117
    wph
    @101
    @118
    @109
    @170
    wb
    @103
    1re
    @24
    c1
    difrp
    sylancl
    mpbid
    #
    rerpdivcld
    remulcld
    #
    @167
    wph
    @131
    @13
    @151
    vn
    csu
    @168
    cle
    wph
    @97
    @151
    vn
    @134
    vk
    cn0
    cR
    @138
    cmul
    co
    #
    cmpt
    #
    cN
    @13
    @49
    @50
    @136
    @137
    @52
    @33
    @5
    @174
    cfv
    #
    @151
    wceq
    @56
    vk
    @5
    @173
    @151
    cn0
    @174
    @57
    @138
    @99
    cR
    cmul
    @141
    oveq2d
    @174
    eqid
    cR
    @99
    cmul
    ovex
    fvmpt
    syl
    #
    @52
    cR
    @99
    @155
    @143
    remulcld
    #
    @159
    @162
    wph
    caddc
    @174
    cN
    cseq
    #
    @168
    cli
    wbr
    @178
    @63
    wcel
    wph
    @148
    cR
    vn
    @139
    @174
    cN
    @13
    @49
    @50
    wph
    cR
    abelthlem7.2
    rpcnd
    #
    @150
    @52
    @140
    @144
    recnd
    @52
    @175
    @151
    @153
    @176
    @161
    eqtr4d
    isermulc2
    #
    @178
    @168
    cli
    caddc
    @174
    cN
    seqex
    cR
    @148
    cmul
    ovex
    breldm
    syl
    isumle
    wph
    @151
    @168
    vn
    @174
    cN
    @13
    @49
    @50
    @176
    @52
    @151
    @177
    recnd
    @180
    isumclim
    breqtrd
    wph
    @168
    cR
    @25
    cdiv
    co
    #
    @130
    @172
    wph
    @181
    wph
    cR
    @25
    abelthlem7.2
    @171
    rpdivcld
    #
    rpred
    #
    @167
    wph
    @168
    @147
    @181
    cmul
    co
    #
    @181
    cle
    wph
    cR
    @147
    @25
    @179
    wph
    @147
    @169
    recnd
    wph
    @25
    @171
    rpcnd
    #
    wph
    @25
    @171
    rpne0d
    div12d
    wph
    @184
    c1
    @181
    cmul
    co
    @181
    cle
    wph
    @147
    c1
    @181
    @169
    wph
    1red
    @183
    wph
    @181
    @182
    rpge0d
    wph
    @101
    @106
    @107
    @55
    @147
    c1
    cle
    wbr
    @103
    @108
    @119
    abelthlem7.3
    @24
    cN
    exple1
    syl31anc
    lemul1ad
    wph
    @181
    wph
    @181
    @182
    rpcnd
    mulid2d
    breqtrd
    eqbrtrd
    wph
    @181
    @130
    cle
    wbr
    #
    cR
    @25
    @130
    cmul
    co
    #
    cle
    wbr
    #
    wph
    cR
    @25
    @81
    cmul
    co
    #
    @23
    cdiv
    co
    #
    @187
    cle
    wph
    cR
    @23
    cmul
    co
    #
    @189
    cle
    wbr
    cR
    @190
    cle
    wbr
    wph
    @191
    cR
    @26
    cmul
    co
    #
    @189
    cle
    wph
    @27
    @191
    @192
    cle
    wbr
    wph
    @22
    @27
    @28
    simprd
    wph
    @23
    @26
    cR
    @88
    wph
    cM
    @25
    abelth.3
    wph
    @118
    @101
    @25
    cr
    wcel
    #
    1re
    @103
    c1
    @24
    resubcl
    sylancr
    #
    remulcld
    abelthlem7.2
    lemul2d
    mpbid
    wph
    @192
    cM
    cR
    @25
    cmul
    co
    #
    cmul
    co
    cM
    @25
    cR
    cmul
    co
    #
    cmul
    co
    @189
    wph
    cR
    cM
    @25
    @179
    wph
    cM
    abelth.3
    recnd
    #
    @185
    mul12d
    wph
    @195
    @196
    cM
    cmul
    wph
    cR
    @25
    @179
    @185
    mulcomd
    oveq2d
    wph
    cM
    @25
    cR
    @197
    @185
    @179
    mul12d
    3eqtrd
    breqtrd
    wph
    cR
    @189
    @23
    @77
    wph
    @25
    @81
    @194
    @83
    remulcld
    @166
    lemuldivd
    mpbid
    wph
    @25
    @81
    @23
    @185
    wph
    @81
    @83
    recnd
    #
    wph
    @23
    @88
    recnd
    wph
    @23
    @166
    rpne0d
    divassd
    breqtrd
    wph
    @127
    @130
    cr
    wcel
    @193
    cc0
    @25
    clt
    wbr
    #
    @186
    @188
    wb
    @77
    @167
    @194
    wph
    @109
    @199
    @117
    wph
    @101
    @118
    @109
    @199
    wb
    @103
    1re
    @24
    c1
    posdif
    sylancl
    mpbid
    cR
    @130
    @25
    ledivmul
    syl112anc
    mpbird
    letrd
    letrd
    letrd
    wph
    @128
    @81
    @23
    @132
    @83
    @166
    lemuldiv2d
    mpbird
    eqbrtrd
    ltleaddd
    wph
    @19
    @81
    c1
    cR
    cmul
    co
    #
    caddc
    co
    @81
    cR
    caddc
    co
    @82
    wph
    cM
    c1
    cR
    @197
    wph
    1cnd
    @179
    adddird
    wph
    @200
    cR
    @81
    caddc
    wph
    cR
    @179
    mulid2d
    oveq2d
    wph
    @81
    cR
    @198
    @179
    addcomd
    3eqtrd
    breqtrrd
    lelttrd
end
