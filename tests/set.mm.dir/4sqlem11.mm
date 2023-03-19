include "crn.mm"
include "cun.mm"
include "chash.mm"
include "cfv.mm"
include "clt.mm"
include "wbr.mm"
include "wn.mm"
include "cin.mm"
include "c0.mm"
include "wne.mm"
include "cle.mm"
include "cc0.mm"
include "c1.mm"
include "cmin.mm"
include "co.mm"
include "cfz.mm"
include "cdom.mm"
include "cfn.mm"
include "wcel.mm"
include "wss.mm"
include "fzfid.mm"
include "cv.mm"
include "c2.mm"
include "cexp.mm"
include "cmo.mm"
include "wceq.mm"
include "wrex.mm"
include "cab.mm"
include "wa.mm"
include "wi.mm"
include "cz.mm"
include "cn.mm"
include "elfzelz.mm"
include "zsqcl.mm"
include "syl.mm"
include "cprime.mm"
include "prmnn.mm"
include "zmodfz.mm"
include "syl2anr.mm"
include "eleq1a.mm"
include "rexlimdva.mm"
include "abssdv.mm"
include "syl5eqss.mm"
include "wf.mm"
include "caddc.mm"
include "prmz.mm"
include "peano2zm.mm"
include "zcnd.mm"
include "addid2d.mm"
include "oveq1d.mm"
include "adantr.mm"
include "sselda.mm"
include "fzrev3i.mm"
include "eqeltrrd.mm"
include "fmptd.mm"
include "frn.mm"
include "unssd.mm"
include "ssdomg.mm"
include "sylc.mm"
include "wb.mm"
include "ssfi.mm"
include "syl2anc.mm"
include "hashdom.mm"
include "mpbird.mm"
include "cen.mm"
include "fz01en.mm"
include "hashen.mm"
include "cn0.mm"
include "nnnn0d.mm"
include "hashfz1.mm"
include "eqtrd.mm"
include "breqtrd.mm"
include "hashcl.mm"
include "nn0red.mm"
include "zred.mm"
include "lenltd.mm"
include "mpbid.mm"
include "cr.mm"
include "ltp1d.mm"
include "nncnd.mm"
include "1cnd.mm"
include "add4d.mm"
include "cmul.mm"
include "cc.mm"
include "2cn.mm"
include "mulcl.mm"
include "sylancr.mm"
include "addassd.mm"
include "2timesd.mm"
include "3eqtrd.mm"
include "cmpt.mm"
include "wf1o.mm"
include "wf1.mm"
include "ex.mm"
include "weq.mm"
include "cdvds.mm"
include "wo.mm"
include "ad2antrl.mm"
include "ad2antll.mm"
include "moddvds.mm"
include "syl3anc.mm"
include "subsq.mm"
include "breq2d.mm"
include "zaddcld.mm"
include "zsubcld.mm"
include "euclemma.mm"
include "3bitrd.mm"
include "2re.mm"
include "nnred.mm"
include "remulcl.mm"
include "elfzle2.mm"
include "le2addd.mm"
include "breqtrrd.mm"
include "lelttrd.mm"
include "ltnled.mm"
include "ad2antrr.mm"
include "cabs.mm"
include "1red.mm"
include "nn0abscl.mm"
include "nn0zd.mm"
include "subeq0ad.mm"
include "necon3bid.mm"
include "biimpar.mm"
include "absrpcld.mm"
include "rpgt0d.mm"
include "elnnz.mm"
include "sylanbrc.mm"
include "nnge1d.mm"
include "0cnd.mm"
include "abs3difd.mm"
include "subid1d.mm"
include "fveq2d.mm"
include "elfzle1.mm"
include "absidd.mm"
include "0cn.mm"
include "abssub.mm"
include "oveq12d.mm"
include "letrd.mm"
include "elnnz1.mm"
include "dvdsle.mm"
include "mtod.mm"
include "necon4ad.mm"
include "dvdsabsb.mm"
include "letr.mm"
include "mpan2d.mm"
include "sylbid.mm"
include "jaod.mm"
include "oveq1.mm"
include "impbid1.mm"
include "dom2lem.mm"
include "f1f1orn.mm"
include "eqid.mm"
include "rnmpt.mm"
include "eqtr4i.mm"
include "f1oeq3.mm"
include "ax-mp.mm"
include "sylibr.mm"
include "ovex.mm"
include "f1oen.mm"
include "ensymd.mm"
include "ax-1cn.mm"
include "pncan.mm"
include "sylancl.mm"
include "oveq2d.mm"
include "peano2nn0.mm"
include "eqbrtrrd.mm"
include "entr.mm"
include "cuz.mm"
include "fzssuz.mm"
include "uzssz.mm"
include "zsscn.mm"
include "sstri.mm"
include "syl6ss.mm"
include "adantrr.mm"
include "adantrl.mm"
include "subcanad.mm"
include "f1eq1.mm"
include "f1oeng.mm"
include "eqtr3d.mm"
include "3eqtr4d.mm"
include "simpr.mm"
include "hashun.mm"
include "eqtr4d.mm"
include "necon3bd.mm"
include "mpd.mm"

theorem 4sqlem11
  let wph: wff ph
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let vw: setvar w
  let vv: setvar v
  let vu: setvar u
  let cA: class A
  let cP: class P
  let cS: class S
  let vm: setvar m
  let vn: setvar n
  let cF: class F
  let cN: class N
  let va: setvar a
  let vb: setvar b
  let vc: setvar c
  let vd: setvar d
  let cB: class B
  let cE: class E
  let cG: class G
  let cH: class H
  let vj: setvar j
  let vk: setvar k
  let cC: class C
  let cD: class D
  let vi: setvar i
  let cM: class M
  let cT: class T
  let cR: class R
  assume 4sq.1: |- S = { n | E. x e. ZZ E. y e. ZZ E. z e. ZZ E. w e. ZZ n = ( ( ( x ^ 2 ) + ( y ^ 2 ) ) + ( ( z ^ 2 ) + ( w ^ 2 ) ) ) }
  assume 4sq.2: |- ( ph -> N e. NN )
  assume 4sq.3: |- ( ph -> P = ( ( 2 x. N ) + 1 ) )
  assume 4sq.4: |- ( ph -> P e. Prime )
  assume 4sqlem11.5: |- A = { u | E. m e. ( 0 ... N ) u = ( ( m ^ 2 ) mod P ) }
  assume 4sqlem11.6: |- F = ( v e. A |-> ( ( P - 1 ) - v ) )

  disjoint n w
  disjoint n x
  disjoint n y
  disjoint n z
  disjoint w x
  disjoint w y
  disjoint w z
  disjoint x y
  disjoint x z
  disjoint y z
  disjoint n v
  disjoint A n
  disjoint A v
  disjoint F n
  disjoint n u
  disjoint m n
  disjoint m u
  disjoint m v
  disjoint N m
  disjoint N n
  disjoint u v
  disjoint N u
  disjoint N v
  disjoint P m
  disjoint P n
  disjoint P u
  disjoint P v
  disjoint m ph
  disjoint n ph
  disjoint ph u
  disjoint ph v
  disjoint S m
  disjoint S n
  disjoint S u
  disjoint S v
  disjoint a b
  disjoint a c
  disjoint a d
  disjoint a n
  disjoint a w
  disjoint a x
  disjoint a y
  disjoint a z
  disjoint b c
  disjoint b d
  disjoint b n
  disjoint b w
  disjoint b x
  disjoint b y
  disjoint b z
  disjoint c d
  disjoint c n
  disjoint c w
  disjoint c x
  disjoint c y
  disjoint c z
  disjoint d n
  disjoint d w
  disjoint d x
  disjoint d y
  disjoint d z
  disjoint B a
  disjoint B b
  disjoint B c
  disjoint B d
  disjoint B n
  disjoint E n
  disjoint G n
  disjoint H n
  disjoint a j
  disjoint a k
  disjoint a v
  disjoint A a
  disjoint b j
  disjoint b k
  disjoint b v
  disjoint A b
  disjoint c j
  disjoint c k
  disjoint c v
  disjoint A c
  disjoint d j
  disjoint d k
  disjoint d v
  disjoint A d
  disjoint j k
  disjoint j n
  disjoint j v
  disjoint A j
  disjoint k n
  disjoint k v
  disjoint A k
  disjoint C a
  disjoint C b
  disjoint C c
  disjoint C d
  disjoint C n
  disjoint D a
  disjoint D b
  disjoint D c
  disjoint D d
  disjoint D n
  disjoint F j
  disjoint a i
  disjoint a u
  disjoint M a
  disjoint b i
  disjoint b u
  disjoint M b
  disjoint c i
  disjoint c u
  disjoint M c
  disjoint d i
  disjoint d u
  disjoint M d
  disjoint i k
  disjoint i n
  disjoint i u
  disjoint M i
  disjoint k u
  disjoint M k
  disjoint M n
  disjoint M u
  disjoint k m
  disjoint N k
  disjoint a m
  disjoint P a
  disjoint b m
  disjoint P b
  disjoint c m
  disjoint P c
  disjoint d m
  disjoint P d
  disjoint i j
  disjoint i m
  disjoint i v
  disjoint P i
  disjoint j m
  disjoint j u
  disjoint P j
  disjoint P k
  disjoint a ph
  disjoint b ph
  disjoint c ph
  disjoint d ph
  disjoint j ph
  disjoint k ph
  disjoint S a
  disjoint S b
  disjoint S c
  disjoint S d
  disjoint S i
  disjoint S j
  disjoint S k
  disjoint T k
  disjoint T u
  disjoint R i
  assert |- ( ph -> ( A i^i ran F ) =/= (/) )

  proof
    wph
    cP
    cA
    cF
    crn
    #
    cun
    #
    chash
    cfv
    #
    clt
    wbr
    #
    wn
    #
    cA
    @0
    cin
    #
    c0
    wne
    wph
    @2
    cP
    cle
    wbr
    @4
    wph
    @2
    cc0
    cP
    c1
    cmin
    co
    #
    cfz
    co
    #
    chash
    cfv
    #
    cP
    cle
    wph
    @2
    @8
    cle
    wbr
    #
    @1
    @7
    cdom
    wbr
    #
    wph
    @7
    cfn
    wcel
    #
    @1
    @7
    wss
    #
    @10
    wph
    cc0
    @6
    fzfid
    #
    wph
    cA
    @0
    @7
    wph
    cA
    vu
    cv
    #
    vm
    cv
    #
    c2
    cexp
    co
    #
    cP
    cmo
    co
    #
    wceq
    #
    vm
    cc0
    cN
    cfz
    co
    #
    wrex
    #
    vu
    cab
    #
    @7
    4sqlem11.5
    wph
    @20
    vu
    @7
    wph
    @18
    @14
    @7
    wcel
    #
    vm
    @19
    wph
    @15
    @19
    wcel
    #
    wa
    @17
    @7
    wcel
    #
    @18
    @22
    wi
    @23
    @16
    cz
    wcel
    #
    cP
    cn
    wcel
    #
    @24
    wph
    @23
    @15
    cz
    wcel
    #
    @25
    @15
    cc0
    cN
    elfzelz
    #
    @15
    zsqcl
    #
    syl
    wph
    cP
    cprime
    wcel
    #
    @26
    4sq.4
    cP
    prmnn
    syl
    #
    @16
    cP
    zmodfz
    syl2anr
    #
    @17
    @7
    @14
    eleq1a
    syl
    rexlimdva
    abssdv
    syl5eqss
    #
    wph
    cA
    @7
    cF
    wf
    @0
    @7
    wss
    #
    wph
    vv
    cA
    @6
    vv
    cv
    #
    cmin
    co
    #
    @7
    cF
    wph
    @35
    cA
    wcel
    #
    wa
    #
    cc0
    @6
    caddc
    co
    #
    @35
    cmin
    co
    #
    @36
    @7
    wph
    @40
    @36
    wceq
    @37
    wph
    @39
    @6
    @35
    cmin
    wph
    @6
    wph
    @6
    wph
    cP
    cz
    wcel
    #
    @6
    cz
    wcel
    wph
    @30
    @41
    4sq.4
    cP
    prmz
    #
    syl
    #
    cP
    peano2zm
    syl
    zcnd
    #
    addid2d
    oveq1d
    adantr
    @38
    @35
    @7
    wcel
    @40
    @7
    wcel
    wph
    cA
    @7
    @35
    @33
    sselda
    @35
    cc0
    @6
    fzrev3i
    syl
    eqeltrrd
    #
    4sqlem11.6
    fmptd
    cA
    @7
    cF
    frn
    syl
    #
    unssd
    #
    @1
    @7
    cfn
    ssdomg
    sylc
    wph
    @1
    cfn
    wcel
    #
    @11
    @9
    @10
    wb
    wph
    @11
    @12
    @48
    @13
    @47
    @7
    @1
    ssfi
    syl2anc
    #
    @13
    @1
    @7
    cfn
    hashdom
    syl2anc
    mpbird
    wph
    @8
    c1
    cP
    cfz
    co
    #
    chash
    cfv
    #
    cP
    wph
    @8
    @51
    wceq
    #
    @7
    @50
    cen
    wbr
    #
    wph
    @41
    @53
    @43
    cP
    fz01en
    syl
    wph
    @11
    @50
    cfn
    wcel
    @52
    @53
    wb
    @13
    wph
    c1
    cP
    fzfid
    @7
    @50
    hashen
    syl2anc
    mpbird
    wph
    cP
    cn0
    wcel
    @51
    cP
    wceq
    wph
    cP
    @31
    nnnn0d
    cP
    hashfz1
    syl
    eqtrd
    breqtrd
    wph
    @2
    cP
    wph
    @2
    wph
    @48
    @2
    cn0
    wcel
    @49
    @1
    hashcl
    syl
    nn0red
    wph
    cP
    @43
    zred
    #
    lenltd
    mpbid
    wph
    @3
    @5
    c0
    wph
    @5
    c0
    wceq
    #
    @3
    wph
    @55
    wa
    #
    cP
    cP
    c1
    caddc
    co
    #
    @2
    clt
    @56
    cP
    wph
    cP
    cr
    wcel
    #
    @55
    @54
    adantr
    ltp1d
    @56
    @57
    cA
    chash
    cfv
    #
    @0
    chash
    cfv
    #
    caddc
    co
    #
    @2
    wph
    @57
    @61
    wceq
    @55
    wph
    cN
    cN
    caddc
    co
    #
    c1
    c1
    caddc
    co
    #
    caddc
    co
    #
    cN
    c1
    caddc
    co
    #
    @65
    caddc
    co
    @57
    @61
    wph
    cN
    cN
    c1
    c1
    wph
    cN
    4sq.2
    nncnd
    #
    @66
    wph
    1cnd
    #
    @67
    add4d
    wph
    @57
    c2
    cN
    cmul
    co
    #
    c1
    caddc
    co
    #
    c1
    caddc
    co
    @68
    @63
    caddc
    co
    @64
    wph
    cP
    @69
    c1
    caddc
    4sq.3
    oveq1d
    wph
    @68
    c1
    c1
    wph
    c2
    cc
    wcel
    cN
    cc
    wcel
    #
    @68
    cc
    wcel
    2cn
    @66
    c2
    cN
    mulcl
    sylancr
    @67
    @67
    addassd
    wph
    @68
    @62
    @63
    caddc
    wph
    cN
    @66
    2timesd
    oveq1d
    3eqtrd
    wph
    @59
    @65
    @60
    @65
    caddc
    wph
    @59
    c1
    @65
    cfz
    co
    #
    chash
    cfv
    #
    @65
    wph
    @59
    @72
    wceq
    #
    cA
    @71
    cen
    wbr
    #
    wph
    cA
    @19
    cen
    wbr
    @19
    @71
    cen
    wbr
    @74
    wph
    @19
    cA
    wph
    @19
    cA
    vm
    @19
    @17
    cmpt
    #
    wf1o
    #
    @19
    cA
    cen
    wbr
    wph
    @19
    @75
    crn
    #
    @75
    wf1o
    #
    @76
    wph
    @19
    @7
    @75
    wf1
    @78
    wph
    vm
    vu
    @19
    @7
    @17
    @14
    c2
    cexp
    co
    #
    cP
    cmo
    co
    #
    wph
    @23
    @24
    @32
    ex
    wph
    @23
    @14
    @19
    wcel
    #
    wa
    #
    @17
    @80
    wceq
    #
    vm
    vu
    weq
    #
    wb
    wph
    @82
    wa
    #
    @83
    @84
    @85
    @83
    cP
    @15
    @14
    caddc
    co
    #
    cdvds
    wbr
    #
    cP
    @15
    @14
    cmin
    co
    #
    cdvds
    wbr
    #
    wo
    #
    @84
    @85
    @83
    cP
    @16
    @79
    cmin
    co
    #
    cdvds
    wbr
    #
    cP
    @86
    @88
    cmul
    co
    #
    cdvds
    wbr
    #
    @90
    @85
    @26
    @25
    @79
    cz
    wcel
    #
    @83
    @92
    wb
    wph
    @26
    @82
    @31
    adantr
    @85
    @27
    @25
    @23
    @27
    wph
    @81
    @28
    ad2antrl
    #
    @29
    syl
    @85
    @14
    cz
    wcel
    #
    @95
    @81
    @97
    wph
    @23
    @14
    cc0
    cN
    elfzelz
    ad2antll
    #
    @14
    zsqcl
    syl
    @16
    @79
    cP
    moddvds
    syl3anc
    @85
    @91
    @93
    cP
    cdvds
    @85
    @15
    cc
    wcel
    @14
    cc
    wcel
    #
    @91
    @93
    wceq
    @85
    @15
    @96
    zcnd
    #
    @85
    @14
    @98
    zcnd
    #
    @15
    @14
    subsq
    syl2anc
    breq2d
    @85
    @30
    @86
    cz
    wcel
    #
    @88
    cz
    wcel
    #
    @94
    @90
    wb
    wph
    @30
    @82
    4sq.4
    adantr
    #
    @85
    @15
    @14
    @96
    @98
    zaddcld
    #
    @85
    @15
    @14
    @96
    @98
    zsubcld
    #
    cP
    @86
    @88
    euclemma
    syl3anc
    3bitrd
    @85
    @87
    @84
    @89
    @85
    @87
    @15
    @14
    @85
    @15
    @14
    wne
    #
    @87
    wn
    @85
    @107
    wa
    #
    @87
    cP
    @86
    cle
    wbr
    #
    @85
    @109
    wn
    #
    @107
    @85
    @86
    cP
    clt
    wbr
    @110
    @85
    @86
    @68
    cP
    @85
    @86
    @105
    zred
    #
    wph
    @68
    cr
    wcel
    #
    @82
    wph
    c2
    cr
    wcel
    cN
    cr
    wcel
    #
    @112
    2re
    wph
    cN
    4sq.2
    nnred
    #
    c2
    cN
    remulcl
    sylancr
    #
    adantr
    @85
    cP
    @85
    @30
    @41
    @104
    @42
    syl
    #
    zred
    #
    @85
    @86
    @62
    @68
    cle
    @85
    @15
    @14
    cN
    cN
    @85
    @15
    @96
    zred
    #
    @85
    @14
    @98
    zred
    #
    wph
    @113
    @82
    @114
    adantr
    #
    @120
    @23
    @15
    cN
    cle
    wbr
    wph
    @81
    @15
    cc0
    cN
    elfzle2
    ad2antrl
    @81
    @14
    cN
    cle
    wbr
    wph
    @23
    @14
    cc0
    cN
    elfzle2
    ad2antll
    le2addd
    @85
    cN
    wph
    @70
    @82
    @66
    adantr
    2timesd
    breqtrrd
    wph
    @68
    cP
    clt
    wbr
    @82
    wph
    @68
    @69
    cP
    clt
    wph
    @68
    @115
    ltp1d
    4sq.3
    breqtrrd
    adantr
    lelttrd
    @85
    @86
    cP
    @111
    @117
    ltnled
    mpbid
    #
    adantr
    @108
    @41
    @86
    cn
    wcel
    #
    @87
    @109
    wi
    wph
    @41
    @82
    @107
    @43
    ad2antrr
    @108
    @102
    c1
    @86
    cle
    wbr
    @122
    @85
    @102
    @107
    @105
    adantr
    #
    @108
    c1
    @88
    cabs
    cfv
    #
    @86
    @108
    1red
    @85
    @124
    cr
    wcel
    #
    @107
    @85
    @124
    @85
    @103
    @124
    cn0
    wcel
    #
    @106
    @88
    nn0abscl
    syl
    #
    nn0red
    #
    adantr
    @108
    @86
    @123
    zred
    @108
    @124
    @108
    @124
    cz
    wcel
    cc0
    @124
    clt
    wbr
    @124
    cn
    wcel
    #
    @108
    @124
    @85
    @126
    @107
    @127
    adantr
    nn0zd
    @108
    @124
    @108
    @88
    @85
    @88
    cc
    wcel
    @107
    @85
    @88
    @106
    zcnd
    adantr
    @85
    @88
    cc0
    wne
    @107
    @85
    @88
    cc0
    @15
    @14
    @85
    @15
    @14
    @100
    @101
    subeq0ad
    necon3bid
    biimpar
    absrpcld
    rpgt0d
    @124
    elnnz
    sylanbrc
    #
    nnge1d
    @85
    @124
    @86
    cle
    wbr
    #
    @107
    @85
    @124
    @15
    cc0
    cmin
    co
    #
    cabs
    cfv
    #
    cc0
    @14
    cmin
    co
    cabs
    cfv
    #
    caddc
    co
    @86
    cle
    @85
    @15
    @14
    cc0
    @100
    @101
    @85
    0cnd
    abs3difd
    @85
    @133
    @15
    @134
    @14
    caddc
    @85
    @133
    @15
    cabs
    cfv
    @15
    @85
    @132
    @15
    cabs
    @85
    @15
    @100
    subid1d
    fveq2d
    @85
    @15
    @118
    @23
    cc0
    @15
    cle
    wbr
    wph
    @81
    @15
    cc0
    cN
    elfzle1
    ad2antrl
    absidd
    eqtrd
    @85
    @134
    @14
    cc0
    cmin
    co
    #
    cabs
    cfv
    #
    @14
    cabs
    cfv
    @14
    @85
    cc0
    cc
    wcel
    @99
    @134
    @136
    wceq
    0cn
    @101
    cc0
    @14
    abssub
    sylancr
    @85
    @135
    @14
    cabs
    @85
    @14
    @101
    subid1d
    fveq2d
    @85
    @14
    @119
    @81
    cc0
    @14
    cle
    wbr
    wph
    @23
    @14
    cc0
    cN
    elfzle1
    ad2antll
    absidd
    3eqtrd
    oveq12d
    breqtrd
    #
    adantr
    letrd
    @86
    elnnz1
    sylanbrc
    cP
    @86
    dvdsle
    syl2anc
    mtod
    ex
    necon4ad
    @85
    @89
    cP
    @124
    cdvds
    wbr
    #
    @84
    @85
    @41
    @103
    @89
    @138
    wb
    @116
    @106
    cP
    @88
    dvdsabsb
    syl2anc
    @85
    @138
    @15
    @14
    @85
    @107
    @138
    wn
    @108
    @138
    cP
    @124
    cle
    wbr
    #
    @85
    @139
    wn
    @107
    @85
    @139
    @109
    @121
    @85
    @139
    @131
    @109
    @137
    @85
    @58
    @125
    @86
    cr
    wcel
    @139
    @131
    wa
    @109
    wi
    @117
    @128
    @111
    cP
    @124
    @86
    letr
    syl3anc
    mpan2d
    mtod
    adantr
    @108
    @41
    @129
    @138
    @139
    wi
    @85
    @41
    @107
    @116
    adantr
    @130
    cP
    @124
    dvdsle
    syl2anc
    mtod
    ex
    necon4ad
    sylbid
    jaod
    sylbid
    @84
    @16
    @79
    cP
    cmo
    @15
    @14
    c2
    cexp
    oveq1
    oveq1d
    impbid1
    ex
    dom2lem
    @19
    @7
    @75
    f1f1orn
    syl
    cA
    @77
    wceq
    @76
    @78
    wb
    cA
    @21
    @77
    4sqlem11.5
    vm
    vu
    @19
    @17
    @75
    @75
    eqid
    rnmpt
    eqtr4i
    cA
    @77
    @19
    @75
    f1oeq3
    ax-mp
    sylibr
    @19
    cA
    @75
    cc0
    cN
    cfz
    ovex
    f1oen
    syl
    ensymd
    wph
    cc0
    @65
    c1
    cmin
    co
    #
    cfz
    co
    #
    @19
    @71
    cen
    wph
    @140
    cN
    cc0
    cfz
    wph
    @70
    c1
    cc
    wcel
    @140
    cN
    wceq
    @66
    ax-1cn
    cN
    c1
    pncan
    sylancl
    oveq2d
    wph
    @65
    cz
    wcel
    @141
    @71
    cen
    wbr
    wph
    @65
    wph
    cN
    cn0
    wcel
    @65
    cn0
    wcel
    #
    wph
    cN
    4sq.2
    nnnn0d
    cN
    peano2nn0
    syl
    #
    nn0zd
    @65
    fz01en
    syl
    eqbrtrrd
    cA
    @19
    @71
    entr
    syl2anc
    wph
    cA
    cfn
    wcel
    #
    @71
    cfn
    wcel
    @73
    @74
    wb
    wph
    @11
    cA
    @7
    wss
    @144
    @13
    @33
    @7
    cA
    ssfi
    syl2anc
    #
    wph
    c1
    @65
    fzfid
    cA
    @71
    hashen
    syl2anc
    mpbird
    wph
    @142
    @72
    @65
    wceq
    @143
    @65
    hashfz1
    syl
    eqtrd
    #
    wph
    @59
    @60
    @65
    wph
    @59
    @60
    wceq
    #
    cA
    @0
    cen
    wbr
    #
    wph
    @144
    cA
    @0
    cF
    wf1o
    #
    @148
    @145
    wph
    cA
    @7
    cF
    wf1
    #
    @149
    wph
    cA
    @7
    vv
    cA
    @36
    cmpt
    #
    wf1
    #
    @150
    wph
    vv
    vk
    cA
    @7
    @36
    @6
    vk
    cv
    #
    cmin
    co
    #
    wph
    @37
    @36
    @7
    wcel
    @45
    ex
    wph
    @37
    @153
    cA
    wcel
    #
    wa
    #
    @36
    @154
    wceq
    vv
    vk
    weq
    wb
    wph
    @156
    wa
    @6
    @35
    @153
    wph
    @6
    cc
    wcel
    @156
    @44
    adantr
    wph
    @37
    @35
    cc
    wcel
    @155
    wph
    cA
    cc
    @35
    wph
    cA
    @7
    cc
    @33
    @7
    cc0
    cuz
    cfv
    #
    cc
    cc0
    @6
    fzssuz
    @157
    cz
    cc
    cc0
    uzssz
    zsscn
    sstri
    sstri
    syl6ss
    #
    sselda
    adantrr
    wph
    @155
    @153
    cc
    wcel
    @37
    wph
    cA
    cc
    @153
    @158
    sselda
    adantrl
    subcanad
    ex
    dom2lem
    cF
    @151
    wceq
    @150
    @152
    wb
    4sqlem11.6
    cA
    @7
    cF
    @151
    f1eq1
    ax-mp
    sylibr
    cA
    @7
    cF
    f1f1orn
    syl
    cA
    @0
    cfn
    cF
    f1oeng
    syl2anc
    wph
    @144
    @0
    cfn
    wcel
    #
    @147
    @148
    wb
    @145
    wph
    @11
    @34
    @159
    @13
    @46
    @7
    @0
    ssfi
    syl2anc
    #
    cA
    @0
    hashen
    syl2anc
    mpbird
    @146
    eqtr3d
    oveq12d
    3eqtr4d
    adantr
    @56
    @144
    @159
    @55
    @2
    @61
    wceq
    wph
    @144
    @55
    @145
    adantr
    wph
    @159
    @55
    @160
    adantr
    wph
    @55
    simpr
    cA
    @0
    hashun
    syl3anc
    eqtr4d
    breqtrd
    ex
    necon3bd
    mpd
end
