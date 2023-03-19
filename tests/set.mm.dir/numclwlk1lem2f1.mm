include "cusgr.mm"
include "wcel.mm"
include "c3.mm"
include "cuz.mm"
include "cfv.mm"
include "w3a.mm"
include "co.mm"
include "cnbgr.mm"
include "cxp.mm"
include "wf.mm"
include "cv.mm"
include "wceq.mm"
include "wi.mm"
include "wral.mm"
include "wf1.mm"
include "numclwlk1lem2f.mm"
include "wa.mm"
include "cc0.mm"
include "c2.mm"
include "cmin.mm"
include "cop.mm"
include "csubstr.mm"
include "c1.mm"
include "numclwlk1lem2fv.mm"
include "ad2antrl.mm"
include "ad2antll.mm"
include "eqeq12d.mm"
include "ovex.mm"
include "fvex.mm"
include "opth.mm"
include "cword.mm"
include "chash.mm"
include "cclwwlkn.mm"
include "wb.mm"
include "uzuzle23.mm"
include "numclwwlkovgel.mm"
include "sylan2.mm"
include "clwwlknbp.mm"
include "3ad2ant1.mm"
include "3simpc.mm"
include "jca.mm"
include "syl6bi.mm"
include "3adant1.mm"
include "clsw.mm"
include "eqtr3.mm"
include "expcom.mm"
include "ad2antlr.mm"
include "com12.mm"
include "imp.mm"
include "oveq1.mm"
include "opeq2d.mm"
include "oveq2d.mm"
include "ad3antlr.mm"
include "adantl.mm"
include "biimprcd.mm"
include "adantr.mm"
include "impcom.mm"
include "eqeq2.mm"
include "eqcoms.mm"
include "fveq2d.mm"
include "eqeq1d.mm"
include "biimpcd.mm"
include "eqeq1.mm"
include "biimpac.mm"
include "sylan9eq.mm"
include "ad4ant24.mm"
include "eqtr4d.mm"
include "lsw.mm"
include "eqeq2d.mm"
include "mpbird.mm"
include "eqeqan12d.mm"
include "biimprd.mm"
include "adantld.mm"
include "3jca.mm"
include "clt.mm"
include "wbr.mm"
include "simpll.mm"
include "simprll.mm"
include "cz.mm"
include "eluz2b1.mm"
include "breq2.mm"
include "simplbiim.mm"
include "syl.mm"
include "3ad2ant3.mm"
include "2swrd2eqwrdeq.mm"
include "exp31.mm"
include "syl2and.mm"
include "syl5bi.mm"
include "sylbid.mm"
include "ralrimivva.mm"
include "dff13.mm"
include "sylanbrc.mm"

theorem numclwlk1lem2f1
  let vw: setvar w
  let vv: setvar v
  let vu: setvar u
  let cC: class C
  let cT: class T
  let vn: setvar n
  let cF: class F
  let cG: class G
  let cN: class N
  let cV: class V
  let cX: class X
  let cW: class W
  let va: setvar a
  let vp: setvar p
  let vi: setvar i
  let cY: class Y
  assume extwwlkfab.v: |- V = ( Vtx ` G )
  assume extwwlkfab.c: |- C = ( v e. V , n e. ( ZZ>= ` 2 ) |-> { w e. ( n ClWWalksN G ) | ( ( w ` 0 ) = v /\ ( w ` ( n - 2 ) ) = ( w ` 0 ) ) } )
  assume extwwlkfab.f: |- F = ( X ( ClWWalksNOn ` G ) ( N - 2 ) )
  assume numclwwlk.t: |- T = ( u e. ( X C N ) |-> <. ( u substr <. 0 , ( N - 2 ) >. ) , ( u ` ( N - 1 ) ) >. )

  disjoint C u
  disjoint G w
  disjoint T u
  disjoint V u
  disjoint G n
  disjoint G v
  disjoint G w
  disjoint n v
  disjoint n w
  disjoint v w
  disjoint V n
  disjoint V v
  disjoint V w
  disjoint X n
  disjoint X v
  disjoint X w
  disjoint N n
  disjoint N v
  disjoint N w
  disjoint F w
  disjoint C u
  disjoint F u
  disjoint G u
  disjoint u w
  disjoint N u
  disjoint V u
  disjoint X u
  disjoint W u
  disjoint C a
  disjoint C p
  disjoint a p
  disjoint a u
  disjoint p u
  disjoint G a
  disjoint G p
  disjoint a w
  disjoint p w
  disjoint N a
  disjoint N p
  disjoint T a
  disjoint T p
  disjoint V a
  disjoint V p
  disjoint X a
  disjoint X p
  disjoint W w
  disjoint G i
  disjoint W i
  disjoint Y w
  assert |- ( ( G e. USGraph /\ X e. V /\ N e. ( ZZ>= ` 3 ) ) -> T : ( X C N ) -1-1-> ( F X. ( G NeighbVtx X ) ) )

  proof
    cG
    cusgr
    wcel
    #
    cX
    cV
    wcel
    #
    cN
    c3
    cuz
    cfv
    wcel
    #
    w3a
    #
    cX
    cN
    cC
    co
    #
    cF
    cG
    cX
    cnbgr
    co
    cxp
    #
    cT
    wf
    vp
    cv
    #
    cT
    cfv
    #
    va
    cv
    #
    cT
    cfv
    #
    wceq
    #
    @6
    @8
    wceq
    #
    wi
    #
    va
    @4
    wral
    vp
    @4
    wral
    @4
    @5
    cT
    wf1
    vw
    vv
    vu
    cC
    cT
    vn
    cF
    cG
    cN
    cV
    cX
    extwwlkfab.v
    extwwlkfab.c
    extwwlkfab.f
    numclwwlk.t
    numclwlk1lem2f
    @3
    @12
    vp
    va
    @4
    @4
    @3
    @6
    @4
    wcel
    #
    @8
    @4
    wcel
    #
    wa
    #
    wa
    #
    @10
    @6
    cc0
    cN
    c2
    cmin
    co
    #
    cop
    #
    csubstr
    co
    #
    cN
    c1
    cmin
    co
    #
    @6
    cfv
    #
    cop
    #
    @8
    @18
    csubstr
    co
    #
    @20
    @8
    cfv
    #
    cop
    #
    wceq
    #
    @11
    @16
    @7
    @22
    @9
    @25
    @13
    @7
    @22
    wceq
    @3
    @14
    vw
    vv
    vu
    cC
    cT
    vn
    cF
    cG
    cN
    cV
    @6
    cX
    extwwlkfab.v
    extwwlkfab.c
    extwwlkfab.f
    numclwwlk.t
    numclwlk1lem2fv
    ad2antrl
    @14
    @9
    @25
    wceq
    @3
    @13
    vw
    vv
    vu
    cC
    cT
    vn
    cF
    cG
    cN
    cV
    @8
    cX
    extwwlkfab.v
    extwwlkfab.c
    extwwlkfab.f
    numclwwlk.t
    numclwlk1lem2fv
    ad2antll
    eqeq12d
    @26
    @19
    @23
    wceq
    #
    @21
    @24
    wceq
    #
    wa
    #
    @16
    @11
    @19
    @21
    @23
    @24
    @6
    @18
    csubstr
    ovex
    @20
    @6
    fvex
    opth
    @3
    @15
    @29
    @11
    wi
    #
    @3
    @13
    @6
    cV
    cword
    #
    wcel
    #
    @6
    chash
    cfv
    #
    cN
    wceq
    #
    wa
    #
    cc0
    @6
    cfv
    #
    cX
    wceq
    #
    @17
    @6
    cfv
    #
    @36
    wceq
    #
    wa
    #
    wa
    #
    @14
    @8
    @31
    wcel
    #
    @8
    chash
    cfv
    #
    cN
    wceq
    #
    wa
    #
    cc0
    @8
    cfv
    #
    cX
    wceq
    #
    @17
    @8
    cfv
    #
    @46
    wceq
    #
    wa
    #
    wa
    #
    @30
    @1
    @2
    @13
    @41
    wi
    @0
    @1
    @2
    wa
    #
    @13
    @6
    cN
    cG
    cclwwlkn
    co
    #
    wcel
    #
    @37
    @39
    w3a
    #
    @41
    @2
    @1
    cN
    c2
    cuz
    cfv
    wcel
    #
    @13
    @55
    wb
    cN
    uzuzle23
    #
    vw
    vv
    cC
    vn
    cG
    cN
    cV
    @6
    cX
    extwwlkfab.c
    numclwwlkovgel
    sylan2
    @55
    @35
    @40
    @54
    @37
    @35
    @39
    cG
    cN
    cV
    @6
    extwwlkfab.v
    clwwlknbp
    3ad2ant1
    @54
    @37
    @39
    3simpc
    jca
    syl6bi
    3adant1
    @1
    @2
    @14
    @51
    wi
    @0
    @52
    @14
    @8
    @53
    wcel
    #
    @47
    @49
    w3a
    #
    @51
    @2
    @1
    @56
    @14
    @59
    wb
    @57
    vw
    vv
    cC
    vn
    cG
    cN
    cV
    @8
    cX
    extwwlkfab.c
    numclwwlkovgel
    sylan2
    @59
    @45
    @50
    @58
    @47
    @45
    @49
    cG
    cN
    cV
    @8
    extwwlkfab.v
    clwwlknbp
    3ad2ant1
    @58
    @47
    @49
    3simpc
    jca
    syl6bi
    3adant1
    @3
    @41
    @51
    wa
    #
    @29
    @11
    @3
    @60
    wa
    #
    @29
    wa
    #
    @11
    @33
    @43
    wceq
    #
    @6
    cc0
    @33
    c2
    cmin
    co
    #
    cop
    #
    csubstr
    co
    #
    @8
    @65
    csubstr
    co
    #
    wceq
    #
    @64
    @6
    cfv
    #
    @64
    @8
    cfv
    #
    wceq
    #
    @6
    clsw
    cfv
    #
    @8
    clsw
    cfv
    #
    wceq
    #
    w3a
    #
    wa
    #
    @62
    @63
    @75
    @60
    @63
    @3
    @29
    @41
    @51
    @63
    @34
    @51
    @63
    wi
    @32
    @40
    @51
    @34
    @63
    @44
    @34
    @63
    wi
    @42
    @50
    @34
    @44
    @63
    @33
    @43
    cN
    eqtr3
    expcom
    ad2antlr
    com12
    ad2antlr
    imp
    ad2antlr
    @62
    @68
    @71
    @74
    @29
    @61
    @68
    @27
    @61
    @68
    wi
    @28
    @61
    @68
    @27
    @60
    @68
    @27
    wb
    #
    @3
    @34
    @77
    @32
    @40
    @51
    @34
    @66
    @19
    @67
    @23
    @34
    @65
    @18
    @6
    csubstr
    @34
    @64
    @17
    cc0
    @33
    cN
    c2
    cmin
    oveq1
    #
    opeq2d
    #
    oveq2d
    @34
    @65
    @18
    @8
    csubstr
    @79
    oveq2d
    eqeq12d
    ad3antlr
    adantl
    biimprcd
    adantr
    impcom
    @60
    @71
    @3
    @29
    @60
    @69
    cX
    @70
    @41
    @69
    cX
    wceq
    #
    @51
    @35
    @40
    @80
    @34
    @40
    @80
    wi
    @32
    @40
    @34
    @80
    @37
    @39
    @34
    @80
    wi
    #
    @37
    @39
    @38
    cX
    wceq
    #
    @81
    @36
    cX
    @38
    eqeq2
    @34
    @82
    @80
    @34
    @38
    @69
    cX
    @34
    @17
    @64
    @6
    @17
    @64
    wceq
    cN
    @33
    cN
    @33
    c2
    cmin
    oveq1
    eqcoms
    fveq2d
    eqeq1d
    biimpcd
    syl6bi
    imp
    com12
    adantl
    imp
    adantr
    @34
    @51
    @70
    cX
    wceq
    @32
    @40
    @34
    @51
    @70
    @48
    cX
    @34
    @64
    @17
    @8
    @78
    fveq2d
    @50
    @48
    cX
    wceq
    #
    @45
    @49
    @47
    @83
    @47
    @83
    wb
    @46
    @48
    @46
    @48
    cX
    eqeq1
    eqcoms
    biimpac
    adantl
    sylan9eq
    ad4ant24
    eqtr4d
    ad2antlr
    @61
    @29
    @74
    @61
    @28
    @74
    @27
    @61
    @74
    @28
    @60
    @74
    @28
    wb
    @3
    @41
    @51
    @72
    @21
    @73
    @24
    @35
    @72
    @21
    wceq
    @40
    @32
    @34
    @72
    @33
    c1
    cmin
    co
    #
    @6
    cfv
    @21
    @6
    @31
    lsw
    @34
    @84
    @20
    @6
    @33
    cN
    c1
    cmin
    oveq1
    fveq2d
    sylan9eq
    adantr
    @45
    @73
    @24
    wceq
    #
    @50
    @45
    @85
    @73
    @43
    c1
    cmin
    co
    #
    @8
    cfv
    #
    wceq
    #
    @42
    @88
    @44
    @8
    @31
    lsw
    adantr
    @44
    @85
    @88
    wb
    @42
    @44
    @24
    @87
    @73
    @44
    @20
    @86
    @8
    @20
    @86
    wceq
    cN
    @43
    cN
    @43
    c1
    cmin
    oveq1
    eqcoms
    fveq2d
    eqeq2d
    adantl
    mpbird
    adantr
    eqeqan12d
    adantl
    biimprd
    adantld
    imp
    3jca
    jca
    @62
    @32
    @42
    c1
    @33
    clt
    wbr
    #
    w3a
    #
    @11
    @76
    wb
    @61
    @90
    @29
    @61
    @32
    @42
    @89
    @41
    @32
    @3
    @51
    @32
    @34
    @40
    simpll
    ad2antrl
    @60
    @42
    @3
    @41
    @42
    @44
    @50
    simprll
    adantl
    @60
    @3
    @89
    @34
    @3
    @89
    wi
    @32
    @40
    @51
    @3
    @34
    @89
    @2
    @0
    @34
    @89
    wi
    #
    @1
    @2
    @56
    @91
    @57
    @56
    cN
    cz
    wcel
    c1
    cN
    clt
    wbr
    #
    @91
    cN
    eluz2b1
    @34
    @92
    @89
    @92
    @89
    wb
    cN
    @33
    cN
    @33
    c1
    clt
    breq2
    eqcoms
    biimpcd
    simplbiim
    syl
    3ad2ant3
    com12
    ad3antlr
    impcom
    3jca
    adantr
    @8
    cV
    @6
    2swrd2eqwrdeq
    syl
    mpbird
    exp31
    syl2and
    imp
    syl5bi
    sylbid
    ralrimivva
    vp
    va
    @4
    @5
    cT
    dff13
    sylanbrc
end
