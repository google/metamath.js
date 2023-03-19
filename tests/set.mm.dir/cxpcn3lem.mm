include "wcel.mm"
include "crp.mm"
include "wa.mm"
include "cv.mm"
include "cabs.mm"
include "cfv.mm"
include "clt.mm"
include "wbr.mm"
include "cmin.mm"
include "co.mm"
include "ccxp.mm"
include "wi.mm"
include "wral.mm"
include "cc0.mm"
include "cpnf.mm"
include "cico.mm"
include "wrex.mm"
include "c1.mm"
include "cdiv.mm"
include "cle.mm"
include "cif.mm"
include "cre.mm"
include "c2.mm"
include "cc.mm"
include "ccnv.mm"
include "cima.mm"
include "eleq2i.mm"
include "cr.mm"
include "wf.mm"
include "wfn.mm"
include "wb.mm"
include "ref.mm"
include "ffn.mm"
include "elpreima.mm"
include "mp2b.mm"
include "bitri.mm"
include "simprbi.mm"
include "adantr.mm"
include "1rp.mm"
include "ifcl.mm"
include "sylancl.mm"
include "rphalfcld.mm"
include "syl5eqel.mm"
include "simpr.mm"
include "rpreccld.mm"
include "rpred.mm"
include "rpcxpcld.mm"
include "ifcld.mm"
include "elrege0.mm"
include "wceq.mm"
include "wo.mm"
include "0red.mm"
include "leloe.mm"
include "sylan.mm"
include "elrp.mm"
include "w3a.mm"
include "simp2l.mm"
include "simp2r.mm"
include "cdm.mm"
include "cnvimass.mm"
include "fdmi.mm"
include "sseqtri.mm"
include "eqsstri.mm"
include "sseli.mm"
include "syl.mm"
include "abscxp.mm"
include "syl2anc.mm"
include "recld.mm"
include "3ad2ant1.mm"
include "simp1r.mm"
include "simp1l.mm"
include "simplbi.mm"
include "rehalfcld.mm"
include "1re.mm"
include "min1.mm"
include "2re.mm"
include "a1i.mm"
include "2pos.mm"
include "lediv1.mm"
include "syl112anc.mm"
include "mpbid.mm"
include "syl5eqbr.mm"
include "caddc.mm"
include "recnd.mm"
include "2halvesd.mm"
include "resubd.mm"
include "subcld.mm"
include "abscld.mm"
include "releabsd.mm"
include "simp3r.mm"
include "syl6breq.mm"
include "ltmin.mm"
include "syl3anc.mm"
include "simpld.mm"
include "lelttrd.mm"
include "ltletrd.mm"
include "eqbrtrrd.mm"
include "ltsubadd2d.mm"
include "eqbrtrd.mm"
include "ltadd1d.mm"
include "mpbird.mm"
include "rprege0d.mm"
include "absid.mm"
include "simp3l.mm"
include "rehalfcl.mm"
include "mp1i.mm"
include "min2.mm"
include "halflt1.mm"
include "lttrd.mm"
include "cxplt3d.mm"
include "cmul.mm"
include "wne.mm"
include "rpcnne0d.mm"
include "recid.mm"
include "oveq2d.mm"
include "rpcnd.mm"
include "cxpmuld.mm"
include "cxp1d.mm"
include "3eqtr3d.mm"
include "simprd.mm"
include "cxplt2.mm"
include "3expia.mm"
include "anassrs.mm"
include "ralrimiva.mm"
include "sylan2br.mm"
include "expr.mm"
include "eleq2s.mm"
include "rpne0d.mm"
include "fveq2.mm"
include "re0.mm"
include "syl6eq.mm"
include "necon3i.mm"
include "0cxpd.mm"
include "adantl.mm"
include "abs00bd.mm"
include "simpllr.mm"
include "rpgt0d.mm"
include "oveq1.mm"
include "fveq2d.mm"
include "breq1d.mm"
include "syl5ibcom.mm"
include "a1dd.mm"
include "ralrimdva.mm"
include "jaod.mm"
include "sylbid.mm"
include "expimpd.mm"
include "syl5bi.mm"
include "ralrimiv.mm"
include "breq2.mm"
include "anbi12d.mm"
include "imbi1d.mm"
include "2ralbidv.mm"
include "rspcev.mm"

theorem cxpcn3lem
  let cA: class A
  let cD: class D
  let cT: class T
  let cU: class U
  let cE: class E
  let cJ: class J
  let cK: class K
  let cL: class L
  let va: setvar a
  let vb: setvar b
  let vd: setvar d
  let ve: setvar e
  let vu: setvar u
  let vv: setvar v
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  assume cxpcn3.d: |- D = ( `' Re " RR+ )
  assume cxpcn3.j: |- J = ( TopOpen ` CCfld )
  assume cxpcn3.k: |- K = ( J |`t ( 0 [,) +oo ) )
  assume cxpcn3.l: |- L = ( J |`t D )
  assume cxpcn3.u: |- U = ( if ( ( Re ` A ) <_ 1 , ( Re ` A ) , 1 ) / 2 )
  assume cxpcn3.t: |- T = if ( U <_ ( E ^c ( 1 / U ) ) , U , ( E ^c ( 1 / U ) ) )

  disjoint a b
  disjoint a d
  disjoint A a
  disjoint b d
  disjoint A b
  disjoint A d
  disjoint E a
  disjoint E b
  disjoint E d
  disjoint J d
  disjoint K a
  disjoint K b
  disjoint K d
  disjoint D a
  disjoint D b
  disjoint D d
  disjoint L a
  disjoint L b
  disjoint L d
  disjoint T a
  disjoint T b
  disjoint T d
  disjoint d e
  disjoint d u
  disjoint d v
  disjoint d x
  disjoint d y
  disjoint d z
  disjoint e u
  disjoint e v
  disjoint e x
  disjoint e y
  disjoint e z
  disjoint J e
  disjoint u v
  disjoint u x
  disjoint u y
  disjoint u z
  disjoint J u
  disjoint v x
  disjoint v y
  disjoint v z
  disjoint J v
  disjoint x y
  disjoint x z
  disjoint J x
  disjoint y z
  disjoint J y
  disjoint J z
  disjoint a e
  disjoint a u
  disjoint a v
  disjoint a z
  disjoint b e
  disjoint b u
  disjoint b v
  disjoint b z
  disjoint K e
  disjoint K u
  disjoint K v
  disjoint K z
  disjoint a x
  disjoint a y
  disjoint b x
  disjoint b y
  disjoint D e
  disjoint D u
  disjoint D v
  disjoint D x
  disjoint D y
  disjoint D z
  disjoint L e
  disjoint L u
  disjoint L v
  disjoint L z
  assert |- ( ( A e. D /\ E e. RR+ ) -> E. d e. RR+ A. a e. ( 0 [,) +oo ) A. b e. D ( ( ( abs ` a ) < d /\ ( abs ` ( A - b ) ) < d ) -> ( abs ` ( a ^c b ) ) < E ) )

  proof
    cA
    cD
    wcel
    #
    cE
    crp
    wcel
    #
    wa
    #
    cT
    crp
    wcel
    va
    cv
    #
    cabs
    cfv
    #
    cT
    clt
    wbr
    #
    cA
    vb
    cv
    #
    cmin
    co
    #
    cabs
    cfv
    #
    cT
    clt
    wbr
    #
    wa
    #
    @3
    @6
    ccxp
    co
    #
    cabs
    cfv
    #
    cE
    clt
    wbr
    #
    wi
    #
    vb
    cD
    wral
    #
    va
    cc0
    cpnf
    cico
    co
    #
    wral
    #
    @4
    vd
    cv
    #
    clt
    wbr
    #
    @8
    @18
    clt
    wbr
    #
    wa
    #
    @13
    wi
    #
    vb
    cD
    wral
    va
    @16
    wral
    #
    vd
    crp
    wrex
    @2
    cT
    cU
    cE
    c1
    cU
    cdiv
    co
    #
    ccxp
    co
    #
    cle
    wbr
    #
    cU
    @25
    cif
    #
    crp
    cxpcn3.t
    @2
    @26
    cU
    @25
    crp
    @2
    cU
    cA
    cre
    cfv
    #
    c1
    cle
    wbr
    #
    @28
    c1
    cif
    #
    c2
    cdiv
    co
    #
    crp
    cxpcn3.u
    @2
    @30
    @2
    @28
    crp
    wcel
    #
    c1
    crp
    wcel
    @30
    crp
    wcel
    #
    @0
    @32
    @1
    @0
    cA
    cc
    wcel
    #
    @32
    @0
    cA
    cre
    ccnv
    crp
    cima
    #
    wcel
    #
    @34
    @32
    wa
    #
    cD
    @35
    cA
    cxpcn3.d
    eleq2i
    cc
    cr
    cre
    wf
    #
    cre
    cc
    wfn
    #
    @36
    @37
    wb
    ref
    cc
    cr
    cre
    ffn
    #
    cc
    cA
    crp
    cre
    elpreima
    mp2b
    bitri
    #
    simprbi
    adantr
    1rp
    @29
    @28
    c1
    crp
    ifcl
    sylancl
    #
    rphalfcld
    syl5eqel
    #
    @2
    cE
    @24
    @0
    @1
    simpr
    @2
    @24
    @2
    cU
    @43
    rpreccld
    rpred
    rpcxpcld
    #
    ifcld
    syl5eqel
    @2
    @15
    va
    @16
    @3
    @16
    wcel
    @3
    cr
    wcel
    #
    cc0
    @3
    cle
    wbr
    #
    wa
    #
    @2
    @15
    @3
    elrege0
    @2
    @45
    @46
    @15
    @2
    @45
    wa
    #
    @46
    cc0
    @3
    clt
    wbr
    #
    cc0
    @3
    wceq
    #
    wo
    #
    @15
    @2
    cc0
    cr
    wcel
    @45
    @46
    @51
    wb
    @2
    0red
    cc0
    @3
    leloe
    sylan
    @48
    @49
    @15
    @50
    @2
    @45
    @49
    @15
    @45
    @49
    wa
    @2
    @3
    crp
    wcel
    #
    @15
    @3
    elrp
    @2
    @52
    wa
    @14
    vb
    cD
    @2
    @52
    @6
    cD
    wcel
    #
    @14
    @2
    @52
    @53
    wa
    #
    @10
    @13
    @2
    @54
    @10
    w3a
    #
    @12
    @3
    @6
    cre
    cfv
    #
    ccxp
    co
    #
    cE
    clt
    @55
    @52
    @6
    cc
    wcel
    #
    @12
    @57
    wceq
    @2
    @52
    @53
    @10
    simp2l
    #
    @55
    @53
    @58
    @2
    @52
    @53
    @10
    simp2r
    cD
    cc
    @6
    cD
    @35
    cc
    cxpcn3.d
    @35
    cre
    cdm
    cc
    cre
    crp
    cnvimass
    cc
    cr
    cre
    ref
    fdmi
    sseqtri
    eqsstri
    sseli
    #
    syl
    #
    @3
    @6
    abscxp
    syl2anc
    @55
    @57
    @3
    cU
    ccxp
    co
    #
    cE
    @55
    @57
    @55
    @3
    @56
    @59
    @55
    @6
    @61
    recld
    #
    rpcxpcld
    rpred
    @55
    @62
    @55
    @3
    cU
    @59
    @55
    cU
    @2
    @54
    cU
    crp
    wcel
    @10
    @43
    3ad2ant1
    #
    rpred
    #
    rpcxpcld
    #
    rpred
    @55
    cE
    @0
    @1
    @54
    @10
    simp1r
    #
    rpred
    @55
    cU
    @56
    clt
    wbr
    @57
    @62
    clt
    wbr
    @55
    cU
    @28
    c2
    cdiv
    co
    #
    @56
    @65
    @55
    @28
    @55
    cA
    @55
    @0
    @34
    @0
    @1
    @54
    @10
    simp1l
    @0
    @34
    @32
    @41
    simplbi
    syl
    #
    recld
    #
    rehalfcld
    #
    @63
    @55
    cU
    @31
    @68
    cle
    cxpcn3.u
    @55
    @30
    @28
    cle
    wbr
    #
    @31
    @68
    cle
    wbr
    #
    @55
    @28
    cr
    wcel
    #
    c1
    cr
    wcel
    #
    @72
    @70
    1re
    @28
    c1
    min1
    sylancl
    @55
    @30
    cr
    wcel
    #
    @74
    c2
    cr
    wcel
    #
    cc0
    c2
    clt
    wbr
    #
    @72
    @73
    wb
    @55
    @30
    @2
    @54
    @33
    @10
    @42
    3ad2ant1
    rpred
    #
    @70
    @77
    @55
    2re
    a1i
    #
    @78
    @55
    2pos
    a1i
    #
    @30
    @28
    c2
    lediv1
    syl112anc
    mpbid
    syl5eqbr
    #
    @55
    @68
    @56
    clt
    wbr
    @68
    @68
    caddc
    co
    #
    @56
    @68
    caddc
    co
    #
    clt
    wbr
    @55
    @83
    @28
    @84
    clt
    @55
    @28
    @55
    @28
    @70
    recnd
    2halvesd
    @55
    @28
    @56
    cmin
    co
    #
    @68
    clt
    wbr
    @28
    @84
    clt
    wbr
    @55
    @7
    cre
    cfv
    #
    @85
    @68
    clt
    @55
    cA
    @6
    @69
    @61
    resubd
    @55
    @86
    cU
    @68
    @55
    @7
    @55
    cA
    @6
    @69
    @61
    subcld
    #
    recld
    #
    @65
    @71
    @55
    @86
    @8
    cU
    @88
    @55
    @7
    @87
    abscld
    #
    @65
    @55
    @7
    @87
    releabsd
    @55
    @8
    cU
    clt
    wbr
    #
    @8
    @25
    clt
    wbr
    #
    @55
    @8
    @27
    clt
    wbr
    #
    @90
    @91
    wa
    #
    @55
    @8
    cT
    @27
    clt
    @2
    @54
    @5
    @9
    simp3r
    cxpcn3.t
    syl6breq
    @55
    @8
    cr
    wcel
    cU
    cr
    wcel
    #
    @25
    cr
    wcel
    #
    @92
    @93
    wb
    @89
    @65
    @55
    @25
    @2
    @54
    @25
    crp
    wcel
    @10
    @44
    3ad2ant1
    rpred
    #
    @8
    cU
    @25
    ltmin
    syl3anc
    mpbid
    simpld
    lelttrd
    @82
    ltletrd
    eqbrtrrd
    @55
    @28
    @56
    @68
    @70
    @63
    @71
    ltsubadd2d
    mpbid
    eqbrtrd
    @55
    @68
    @56
    @68
    @71
    @63
    @71
    ltadd1d
    mpbird
    lelttrd
    @55
    @3
    cU
    @56
    @59
    @65
    @55
    @3
    cU
    c1
    @55
    @3
    @59
    rpred
    #
    @65
    @75
    @55
    1re
    a1i
    #
    @55
    @3
    cU
    clt
    wbr
    #
    @3
    @25
    clt
    wbr
    #
    @55
    @3
    @27
    clt
    wbr
    #
    @99
    @100
    wa
    #
    @55
    @3
    cT
    @27
    clt
    @55
    @4
    @3
    cT
    clt
    @55
    @47
    @4
    @3
    wceq
    @55
    @3
    @59
    rprege0d
    @3
    absid
    syl
    @2
    @54
    @5
    @9
    simp3l
    eqbrtrrd
    cxpcn3.t
    syl6breq
    @55
    @45
    @94
    @95
    @101
    @102
    wb
    @97
    @65
    @96
    @3
    cU
    @25
    ltmin
    syl3anc
    mpbid
    #
    simpld
    @55
    cU
    c1
    c2
    cdiv
    co
    #
    c1
    @65
    @75
    @104
    cr
    wcel
    @55
    1re
    c1
    rehalfcl
    mp1i
    @98
    @55
    cU
    @31
    @104
    cle
    cxpcn3.u
    @55
    @30
    c1
    cle
    wbr
    #
    @31
    @104
    cle
    wbr
    #
    @55
    @74
    @75
    @105
    @70
    1re
    @28
    c1
    min2
    sylancl
    @55
    @76
    @75
    @77
    @78
    @105
    @106
    wb
    @79
    @98
    @80
    @81
    @30
    c1
    c2
    lediv1
    syl112anc
    mpbid
    syl5eqbr
    @104
    c1
    clt
    wbr
    @55
    halflt1
    a1i
    lelttrd
    lttrd
    @63
    cxplt3d
    mpbid
    @55
    @62
    cE
    clt
    wbr
    #
    @62
    @24
    ccxp
    co
    #
    @25
    clt
    wbr
    #
    @55
    @108
    @3
    @25
    clt
    @55
    @3
    cU
    @24
    cmul
    co
    #
    ccxp
    co
    @3
    c1
    ccxp
    co
    @108
    @3
    @55
    @110
    c1
    @3
    ccxp
    @55
    cU
    cc
    wcel
    cU
    cc0
    wne
    wa
    @110
    c1
    wceq
    @55
    cU
    @64
    rpcnne0d
    cU
    recid
    syl
    oveq2d
    @55
    @3
    cU
    @24
    @59
    @65
    @55
    @24
    @55
    cU
    @64
    rpreccld
    #
    rpcnd
    cxpmuld
    @55
    @3
    @55
    @3
    @59
    rpcnd
    cxp1d
    3eqtr3d
    @55
    @99
    @100
    @103
    simprd
    eqbrtrd
    @55
    @62
    cr
    wcel
    cc0
    @62
    cle
    wbr
    wa
    cE
    cr
    wcel
    cc0
    cE
    cle
    wbr
    wa
    @24
    crp
    wcel
    @107
    @109
    wb
    @55
    @62
    @66
    rprege0d
    @55
    cE
    @67
    rprege0d
    @111
    @62
    cE
    @24
    cxplt2
    syl3anc
    mpbird
    lttrd
    eqbrtrd
    3expia
    anassrs
    ralrimiva
    sylan2br
    expr
    @48
    @50
    @14
    vb
    cD
    @48
    @53
    wa
    #
    @50
    @13
    @10
    @112
    cc0
    @6
    ccxp
    co
    #
    cabs
    cfv
    #
    cE
    clt
    wbr
    @50
    @13
    @112
    @114
    cc0
    cE
    clt
    @112
    @113
    @53
    @113
    cc0
    wceq
    @48
    @53
    @6
    @60
    @53
    @56
    cc0
    wne
    @6
    cc0
    wne
    @53
    @56
    @56
    crp
    wcel
    #
    @6
    @35
    cD
    @6
    @35
    wcel
    #
    @58
    @115
    @38
    @39
    @116
    @58
    @115
    wa
    wb
    ref
    @40
    cc
    @6
    crp
    cre
    elpreima
    mp2b
    simprbi
    cxpcn3.d
    eleq2s
    rpne0d
    @6
    cc0
    @56
    cc0
    @6
    cc0
    wceq
    @56
    cc0
    cre
    cfv
    cc0
    @6
    cc0
    cre
    fveq2
    re0
    syl6eq
    necon3i
    syl
    0cxpd
    adantl
    abs00bd
    @112
    cE
    @0
    @1
    @45
    @53
    simpllr
    rpgt0d
    eqbrtrd
    @50
    @114
    @12
    cE
    clt
    @50
    @113
    @11
    cabs
    cc0
    @3
    @6
    ccxp
    oveq1
    fveq2d
    breq1d
    syl5ibcom
    a1dd
    ralrimdva
    jaod
    sylbid
    expimpd
    syl5bi
    ralrimiv
    @23
    @17
    vd
    cT
    crp
    @18
    cT
    wceq
    #
    @22
    @14
    va
    vb
    @16
    cD
    @117
    @21
    @10
    @13
    @117
    @19
    @5
    @20
    @9
    @18
    cT
    @4
    clt
    breq2
    @18
    cT
    @8
    clt
    breq2
    anbi12d
    imbi1d
    2ralbidv
    rspcev
    syl2anc
end
