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
include "wrex.mm"
include "wral.mm"
include "wfo.mm"
include "numclwlk1lem2f.mm"
include "cop.mm"
include "wa.mm"
include "wex.mm"
include "wi.mm"
include "elxp.mm"
include "cs1.mm"
include "cconcat.mm"
include "numclwlk1lem2foa.mm"
include "com12.mm"
include "adantl.mm"
include "imp.mm"
include "cc0.mm"
include "c2.mm"
include "cmin.mm"
include "csubstr.mm"
include "c1.mm"
include "simpl.mm"
include "fveq2.mm"
include "eqeq2d.mm"
include "numclwlk1lem2fv.mm"
include "adantr.mm"
include "sylan9bbr.mm"
include "simprll.mm"
include "nbgrisvtx.mm"
include "cword.mm"
include "caddc.mm"
include "cpr.mm"
include "cedg.mm"
include "chash.mm"
include "cfzo.mm"
include "clsw.mm"
include "cclwwlknon.mm"
include "eleq2i.mm"
include "wne.mm"
include "wb.mm"
include "uz3m2nn.mm"
include "nnne0d.mm"
include "3ad2ant3.mm"
include "eqid.mm"
include "clwwlknonel.mm"
include "syl.mm"
include "syl5bb.mm"
include "df-3an.mm"
include "syl6bb.mm"
include "simplll.mm"
include "s1cl.mm"
include "ccatass.mm"
include "oveq1d.mm"
include "syl3anc.mm"
include "ccatcl.mm"
include "syl2an.mm"
include "simpr.mm"
include "eqcomd.mm"
include "swrdccatid.mm"
include "eqtr2d.mm"
include "1e2m1.mm"
include "a1i.mm"
include "oveq2d.mm"
include "eluzelcn.mm"
include "2cnd.mm"
include "1cnd.mm"
include "subsubd.mm"
include "eqtrd.mm"
include "fveq2d.mm"
include "simpll.mm"
include "simprl.mm"
include "anim1i.mm"
include "ccatw2s1p2.mm"
include "syl2anc.mm"
include "opeq12d.mm"
include "exp31.mm"
include "3ad2antl1.mm"
include "3adant1.mm"
include "sylbid.mm"
include "com23.mm"
include "syl5.mm"
include "com13.mm"
include "rspcedvd.mm"
include "mpancom.mm"
include "ex.mm"
include "exlimivv.mm"
include "sylbi.mm"
include "impcom.mm"
include "ralrimiva.mm"
include "dffo3.mm"
include "sylanbrc.mm"

theorem numclwlk1lem2fo
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
  let vb: setvar b
  let vx: setvar x
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
  disjoint C b
  disjoint C x
  disjoint a b
  disjoint a x
  disjoint b p
  disjoint b x
  disjoint p x
  disjoint F a
  disjoint F b
  disjoint F p
  disjoint F x
  disjoint G b
  disjoint G x
  disjoint b w
  disjoint w x
  disjoint N b
  disjoint N x
  disjoint T b
  disjoint T x
  disjoint V b
  disjoint V x
  disjoint X b
  disjoint X x
  disjoint a i
  disjoint b u
  disjoint W w
  disjoint G i
  disjoint W i
  disjoint Y w
  assert |- ( ( G e. USGraph /\ X e. V /\ N e. ( ZZ>= ` 3 ) ) -> T : ( X C N ) -onto-> ( F X. ( G NeighbVtx X ) ) )

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
    #
    cxp
    #
    cT
    wf
    vp
    cv
    #
    vx
    cv
    #
    cT
    cfv
    #
    wceq
    #
    vx
    @4
    wrex
    #
    vp
    @6
    wral
    @4
    @6
    cT
    wfo
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
    @11
    vp
    @6
    @7
    @6
    wcel
    #
    @3
    @11
    @12
    @7
    va
    cv
    #
    vb
    cv
    #
    cop
    #
    wceq
    #
    @13
    cF
    wcel
    #
    @14
    @5
    wcel
    #
    wa
    #
    wa
    #
    vb
    wex
    va
    wex
    @3
    @11
    wi
    #
    va
    vb
    @7
    cF
    @5
    elxp
    @20
    @21
    va
    vb
    @20
    @3
    @11
    @13
    cX
    cs1
    #
    cconcat
    co
    @14
    cs1
    #
    cconcat
    co
    #
    @4
    wcel
    #
    @20
    @3
    wa
    #
    @11
    @20
    @3
    @25
    @19
    @3
    @25
    wi
    @16
    @3
    @19
    @25
    vw
    vv
    cC
    vn
    cF
    cG
    cN
    cV
    @13
    cX
    @14
    extwwlkfab.v
    extwwlkfab.c
    extwwlkfab.f
    numclwlk1lem2foa
    com12
    adantl
    imp
    @25
    @26
    wa
    #
    @10
    @7
    @24
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
    @24
    cfv
    #
    cop
    #
    wceq
    #
    vx
    @24
    @4
    @25
    @26
    simpl
    @8
    @24
    wceq
    #
    @10
    @7
    @24
    cT
    cfv
    #
    wceq
    @27
    @34
    @35
    @9
    @36
    @7
    @8
    @24
    cT
    fveq2
    eqeq2d
    @27
    @36
    @33
    @7
    @25
    @36
    @33
    wceq
    @26
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
    @24
    cX
    extwwlkfab.v
    extwwlkfab.c
    extwwlkfab.f
    numclwwlk.t
    numclwlk1lem2fv
    adantr
    eqeq2d
    sylan9bbr
    @27
    @7
    @15
    @33
    @25
    @16
    @19
    @3
    simprll
    @26
    @15
    @33
    wceq
    #
    @25
    @20
    @3
    @37
    @19
    @3
    @37
    wi
    #
    @16
    @17
    @18
    @38
    @3
    @18
    @17
    @37
    @18
    @14
    cV
    wcel
    #
    @3
    @17
    @37
    wi
    cG
    cX
    @14
    cV
    extwwlkfab.v
    nbgrisvtx
    @3
    @17
    @39
    @37
    @3
    @17
    @13
    cV
    cword
    #
    wcel
    #
    vi
    cv
    #
    @13
    cfv
    @42
    c1
    caddc
    co
    @13
    cfv
    cpr
    cG
    cedg
    cfv
    #
    wcel
    vi
    cc0
    @13
    chash
    cfv
    #
    c1
    cmin
    co
    cfzo
    co
    wral
    #
    @13
    clsw
    cfv
    cc0
    @13
    cfv
    #
    cpr
    @43
    wcel
    #
    w3a
    #
    @44
    @28
    wceq
    #
    wa
    #
    @46
    cX
    wceq
    #
    wa
    #
    @39
    @37
    wi
    #
    @3
    @17
    @48
    @49
    @51
    w3a
    #
    @52
    @17
    @13
    cX
    @28
    cG
    cclwwlknon
    cfv
    co
    #
    wcel
    #
    @3
    @54
    cF
    @55
    @13
    extwwlkfab.f
    eleq2i
    @3
    @28
    cc0
    wne
    #
    @56
    @54
    wb
    @2
    @0
    @57
    @1
    @2
    @28
    cN
    uz3m2nn
    nnne0d
    3ad2ant3
    vi
    @43
    cG
    @28
    cV
    @13
    cX
    extwwlkfab.v
    @43
    eqid
    clwwlknonel
    syl
    syl5bb
    @48
    @49
    @51
    df-3an
    syl6bb
    @1
    @2
    @52
    @53
    wi
    @0
    @52
    @1
    @2
    wa
    #
    @53
    @50
    @58
    @53
    wi
    #
    @51
    @41
    @45
    @49
    @59
    @47
    @41
    @49
    wa
    #
    @58
    @39
    @37
    @60
    @58
    wa
    #
    @39
    wa
    #
    @13
    @30
    @14
    @32
    @62
    @30
    @13
    @22
    @23
    cconcat
    co
    #
    cconcat
    co
    #
    @29
    csubstr
    co
    #
    @13
    @62
    @41
    @22
    @40
    wcel
    #
    @23
    @40
    wcel
    #
    @30
    @65
    wceq
    @41
    @49
    @58
    @39
    simplll
    #
    @61
    @66
    @39
    @58
    @66
    @60
    @1
    @66
    @2
    cX
    cV
    s1cl
    adantr
    adantl
    #
    adantr
    @39
    @67
    @61
    @14
    cV
    s1cl
    #
    adantl
    @41
    @66
    @67
    w3a
    @24
    @64
    @29
    csubstr
    cV
    @13
    @22
    @23
    ccatass
    oveq1d
    syl3anc
    @62
    @41
    @63
    @40
    wcel
    #
    @28
    @44
    wceq
    #
    @65
    @13
    wceq
    @68
    @61
    @66
    @67
    @71
    @39
    @69
    @70
    cV
    @22
    @23
    ccatcl
    syl2an
    @61
    @72
    @39
    @60
    @72
    @58
    @60
    @44
    @28
    @41
    @49
    simpr
    eqcomd
    adantr
    adantr
    @13
    @63
    @28
    cV
    swrdccatid
    syl3anc
    eqtr2d
    @62
    @32
    @28
    c1
    caddc
    co
    #
    @24
    cfv
    #
    @14
    @62
    @31
    @73
    @24
    @61
    @31
    @73
    wceq
    #
    @39
    @58
    @75
    @60
    @2
    @75
    @1
    @2
    @31
    cN
    c2
    c1
    cmin
    co
    #
    cmin
    co
    @73
    @2
    c1
    @76
    cN
    cmin
    c1
    @76
    wceq
    @2
    1e2m1
    a1i
    oveq2d
    @2
    cN
    c2
    c1
    c3
    cN
    eluzelcn
    @2
    2cnd
    @2
    1cnd
    subsubd
    eqtrd
    adantl
    adantl
    adantr
    fveq2d
    @62
    @60
    @1
    @39
    wa
    @74
    @14
    wceq
    @60
    @58
    @39
    simpll
    @61
    @1
    @39
    @60
    @1
    @2
    simprl
    anim1i
    @28
    cV
    @13
    cX
    @14
    ccatw2s1p2
    syl2anc
    eqtr2d
    opeq12d
    exp31
    3ad2antl1
    adantr
    com12
    3adant1
    sylbid
    com23
    syl5
    com13
    imp
    adantl
    imp
    adantl
    eqtrd
    rspcedvd
    mpancom
    ex
    exlimivv
    sylbi
    impcom
    ralrimiva
    vx
    vp
    @4
    @6
    cT
    dffo3
    sylanbrc
end
