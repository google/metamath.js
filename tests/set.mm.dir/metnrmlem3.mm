include "wcel.mm"
include "wss.mm"
include "cin.mm"
include "c0.mm"
include "wceq.mm"
include "cv.mm"
include "w3a.mm"
include "wrex.mm"
include "incom.mm"
include "syl5eq.mm"
include "metnrmlem2.mm"
include "simpld.mm"
include "simprd.mm"
include "c1.mm"
include "cfv.mm"
include "cle.mm"
include "wbr.mm"
include "cif.mm"
include "c2.mm"
include "cdiv.mm"
include "co.mm"
include "cbl.mm"
include "ciun.mm"
include "ineq1i.mm"
include "iunin1.mm"
include "eqtr4i.mm"
include "wral.mm"
include "wa.mm"
include "ineq2i.mm"
include "iunin2.mm"
include "cxmt.mm"
include "cxr.mm"
include "cxad.mm"
include "adantr.mm"
include "cuni.mm"
include "ccld.mm"
include "eqid.mm"
include "cldss.mm"
include "syl.mm"
include "mopnuni.mm"
include "sseqtr4d.mm"
include "sselda.mm"
include "adantrr.mm"
include "adantrl.mm"
include "crp.mm"
include "cc0.mm"
include "clt.mm"
include "metnrmlem1a.mm"
include "rphalfcld.mm"
include "rpxrd.mm"
include "caddc.mm"
include "cr.mm"
include "rpred.mm"
include "rehalfcld.mm"
include "rexadd.mm"
include "syl2anc.mm"
include "recnd.mm"
include "2cnd.mm"
include "wne.mm"
include "2ne0.mm"
include "a1i.mm"
include "divdird.mm"
include "eqtr4d.mm"
include "cxmu.mm"
include "metnrmlem1.mm"
include "ancom2s.mm"
include "xmetsym.mm"
include "syl3anc.mm"
include "breqtrd.mm"
include "wi.mm"
include "xmetcl.mm"
include "xle2add.mm"
include "syl22anc.mm"
include "mp2and.mm"
include "cmul.mm"
include "readdcld.mm"
include "divcan2d.mm"
include "2re.mm"
include "rexmul.mm"
include "sylancr.mm"
include "3eqtr4d.mm"
include "x2times.mm"
include "3brtr4d.mm"
include "wb.mm"
include "rexrd.mm"
include "2rp.mm"
include "xlemul2.mm"
include "mpbird.mm"
include "eqbrtrd.mm"
include "bldisj.mm"
include "syl33anc.mm"
include "eqimss.mm"
include "anassrs.mm"
include "ralrimiva.mm"
include "iunss.mm"
include "sylibr.mm"
include "syl5eqss.mm"
include "ss0.mm"
include "sseq2.mm"
include "ineq1.mm"
include "eqeq1d.mm"
include "3anbi13d.mm"
include "ineq2.mm"
include "3anbi23d.mm"
include "rspc2ev.mm"
include "syl113anc.mm"

theorem metnrmlem3
  let wph: wff ph
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let vw: setvar w
  let vt: setvar t
  let cD: class D
  let cS: class S
  let cT: class T
  let cU: class U
  let cF: class F
  let cG: class G
  let cJ: class J
  let cV: class V
  let cX: class X
  let vs: setvar s
  let vr: setvar r
  let cA: class A
  let cB: class B
  let cC: class C
  let cR: class R
  let cK: class K
  assume metdscn.f: |- F = ( x e. X |-> inf ( ran ( y e. S |-> ( x D y ) ) , RR* , < ) )
  assume metdscn.j: |- J = ( MetOpen ` D )
  assume metnrmlem.1: |- ( ph -> D e. ( *Met ` X ) )
  assume metnrmlem.2: |- ( ph -> S e. ( Clsd ` J ) )
  assume metnrmlem.3: |- ( ph -> T e. ( Clsd ` J ) )
  assume metnrmlem.4: |- ( ph -> ( S i^i T ) = (/) )
  assume metnrmlem.u: |- U = U_ t e. T ( t ( ball ` D ) ( if ( 1 <_ ( F ` t ) , 1 , ( F ` t ) ) / 2 ) )
  assume metnrmlem.g: |- G = ( x e. X |-> inf ( ran ( y e. T |-> ( x D y ) ) , RR* , < ) )
  assume metnrmlem.v: |- V = U_ s e. S ( s ( ball ` D ) ( if ( 1 <_ ( G ` s ) , 1 , ( G ` s ) ) / 2 ) )

  disjoint w x
  disjoint w y
  disjoint w z
  disjoint x y
  disjoint x z
  disjoint y z
  disjoint s t
  disjoint s w
  disjoint s x
  disjoint s y
  disjoint s z
  disjoint D s
  disjoint t w
  disjoint t x
  disjoint t y
  disjoint t z
  disjoint D t
  disjoint D w
  disjoint D x
  disjoint D y
  disjoint D z
  disjoint J s
  disjoint J t
  disjoint J w
  disjoint J y
  disjoint J z
  disjoint ph s
  disjoint ph t
  disjoint G s
  disjoint G t
  disjoint T s
  disjoint T t
  disjoint T w
  disjoint T x
  disjoint T y
  disjoint T z
  disjoint S s
  disjoint S t
  disjoint S w
  disjoint S x
  disjoint S y
  disjoint S z
  disjoint U s
  disjoint U w
  disjoint X s
  disjoint X t
  disjoint X w
  disjoint X x
  disjoint X y
  disjoint X z
  disjoint F s
  disjoint F t
  disjoint F w
  disjoint F z
  disjoint V w
  disjoint V z
  disjoint r w
  disjoint r x
  disjoint r y
  disjoint r z
  disjoint A r
  disjoint A w
  disjoint A x
  disjoint A y
  disjoint A z
  disjoint r s
  disjoint r t
  disjoint D r
  disjoint J r
  disjoint B x
  disjoint B y
  disjoint C r
  disjoint C s
  disjoint C w
  disjoint C z
  disjoint R w
  disjoint R z
  disjoint K r
  disjoint K s
  disjoint K w
  disjoint K z
  disjoint S r
  disjoint X r
  disjoint F r
  assert |- ( ph -> E. z e. J E. w e. J ( S C_ z /\ T C_ w /\ ( z i^i w ) = (/) ) )

  proof
    wph
    cV
    cJ
    wcel
    #
    cU
    cJ
    wcel
    #
    cS
    cV
    wss
    #
    cT
    cU
    wss
    #
    cV
    cU
    cin
    #
    c0
    wceq
    #
    cS
    vz
    cv
    #
    wss
    #
    cT
    vw
    cv
    #
    wss
    #
    @6
    @8
    cin
    #
    c0
    wceq
    #
    w3a
    #
    vw
    cJ
    wrex
    vz
    cJ
    wrex
    wph
    @0
    @2
    wph
    vx
    vy
    vs
    cD
    cT
    cS
    cV
    cG
    cJ
    cX
    metnrmlem.g
    metdscn.j
    metnrmlem.1
    metnrmlem.3
    metnrmlem.2
    wph
    cT
    cS
    cin
    cS
    cT
    cin
    c0
    cT
    cS
    incom
    metnrmlem.4
    syl5eq
    #
    metnrmlem.v
    metnrmlem2
    #
    simpld
    wph
    @1
    @3
    wph
    vx
    vy
    vt
    cD
    cS
    cT
    cU
    cF
    cJ
    cX
    metdscn.f
    metdscn.j
    metnrmlem.1
    metnrmlem.2
    metnrmlem.3
    metnrmlem.4
    metnrmlem.u
    metnrmlem2
    #
    simpld
    wph
    @0
    @2
    @14
    simprd
    wph
    @1
    @3
    @15
    simprd
    wph
    @4
    vs
    cS
    vs
    cv
    #
    c1
    @16
    cG
    cfv
    #
    cle
    wbr
    c1
    @17
    cif
    #
    c2
    cdiv
    co
    #
    cD
    cbl
    cfv
    #
    co
    #
    cU
    cin
    #
    ciun
    #
    c0
    @4
    vs
    cS
    @21
    ciun
    #
    cU
    cin
    @23
    cV
    @24
    cU
    metnrmlem.v
    ineq1i
    vs
    cS
    cU
    @21
    iunin1
    eqtr4i
    wph
    @23
    c0
    wss
    #
    @23
    c0
    wceq
    wph
    @22
    c0
    wss
    #
    vs
    cS
    wral
    @25
    wph
    @26
    vs
    cS
    wph
    @16
    cS
    wcel
    #
    wa
    #
    @22
    vt
    cT
    @21
    vt
    cv
    #
    c1
    @29
    cF
    cfv
    #
    cle
    wbr
    c1
    @30
    cif
    #
    c2
    cdiv
    co
    #
    @20
    co
    #
    cin
    #
    ciun
    #
    c0
    @22
    @21
    vt
    cT
    @33
    ciun
    #
    cin
    @35
    cU
    @36
    @21
    metnrmlem.u
    ineq2i
    vt
    cT
    @21
    @33
    iunin2
    eqtr4i
    @28
    @34
    c0
    wss
    #
    vt
    cT
    wral
    @35
    c0
    wss
    @28
    @37
    vt
    cT
    wph
    @27
    @29
    cT
    wcel
    #
    @37
    wph
    @27
    @38
    wa
    #
    wa
    #
    @34
    c0
    wceq
    #
    @37
    @40
    cD
    cX
    cxmt
    cfv
    wcel
    #
    @16
    cX
    wcel
    #
    @29
    cX
    wcel
    #
    @19
    cxr
    wcel
    @32
    cxr
    wcel
    @19
    @32
    cxad
    co
    #
    @16
    @29
    cD
    co
    #
    cle
    wbr
    @41
    wph
    @42
    @39
    metnrmlem.1
    adantr
    #
    wph
    @27
    @43
    @38
    wph
    cS
    cX
    @16
    wph
    cS
    cJ
    cuni
    #
    cX
    wph
    cS
    cJ
    ccld
    cfv
    #
    wcel
    cS
    @48
    wss
    metnrmlem.2
    cS
    cJ
    @48
    @48
    eqid
    #
    cldss
    syl
    wph
    @42
    cX
    @48
    wceq
    metnrmlem.1
    cD
    cJ
    cX
    metdscn.j
    mopnuni
    syl
    #
    sseqtr4d
    sselda
    adantrr
    #
    wph
    @38
    @44
    @27
    wph
    cT
    cX
    @29
    wph
    cT
    @48
    cX
    wph
    cT
    @49
    wcel
    cT
    @48
    wss
    metnrmlem.3
    cT
    cJ
    @48
    @50
    cldss
    syl
    @51
    sseqtr4d
    sselda
    adantrl
    #
    @40
    @19
    @40
    @18
    wph
    @27
    @18
    crp
    wcel
    #
    @38
    @28
    cc0
    @17
    clt
    wbr
    @54
    wph
    vx
    vy
    @16
    cD
    cT
    cS
    cG
    cJ
    cX
    metnrmlem.g
    metdscn.j
    metnrmlem.1
    metnrmlem.3
    metnrmlem.2
    @13
    metnrmlem1a
    simprd
    adantrr
    #
    rphalfcld
    rpxrd
    @40
    @32
    @40
    @31
    @40
    cc0
    @30
    clt
    wbr
    #
    @31
    crp
    wcel
    #
    wph
    @38
    @56
    @57
    wa
    @27
    wph
    vx
    vy
    @29
    cD
    cS
    cT
    cF
    cJ
    cX
    metdscn.f
    metdscn.j
    metnrmlem.1
    metnrmlem.2
    metnrmlem.3
    metnrmlem.4
    metnrmlem1a
    adantrl
    simprd
    #
    rphalfcld
    rpxrd
    @40
    @45
    @18
    @31
    caddc
    co
    #
    c2
    cdiv
    co
    #
    @46
    cle
    @40
    @45
    @19
    @32
    caddc
    co
    #
    @60
    @40
    @19
    cr
    wcel
    @32
    cr
    wcel
    @45
    @61
    wceq
    @40
    @18
    @40
    @18
    @55
    rpred
    #
    rehalfcld
    @40
    @31
    @40
    @31
    @58
    rpred
    #
    rehalfcld
    @19
    @32
    rexadd
    syl2anc
    @40
    @18
    @31
    c2
    @40
    @18
    @62
    recnd
    @40
    @31
    @63
    recnd
    @40
    2cnd
    #
    c2
    cc0
    wne
    @40
    2ne0
    a1i
    #
    divdird
    eqtr4d
    @40
    @60
    @46
    cle
    wbr
    #
    c2
    @60
    cxmu
    co
    #
    c2
    @46
    cxmu
    co
    #
    cle
    wbr
    #
    @40
    @18
    @31
    cxad
    co
    #
    @46
    @46
    cxad
    co
    #
    @67
    @68
    cle
    @40
    @18
    @46
    cle
    wbr
    #
    @31
    @46
    cle
    wbr
    #
    @70
    @71
    cle
    wbr
    #
    @40
    @18
    @29
    @16
    cD
    co
    #
    @46
    cle
    wph
    @38
    @27
    @18
    @75
    cle
    wbr
    wph
    vx
    vy
    @29
    @16
    cD
    cT
    cS
    cG
    cJ
    cX
    metnrmlem.g
    metdscn.j
    metnrmlem.1
    metnrmlem.3
    metnrmlem.2
    @13
    metnrmlem1
    ancom2s
    @40
    @42
    @44
    @43
    @75
    @46
    wceq
    @47
    @53
    @52
    @29
    @16
    cD
    cX
    xmetsym
    syl3anc
    breqtrd
    wph
    vx
    vy
    @16
    @29
    cD
    cS
    cT
    cF
    cJ
    cX
    metdscn.f
    metdscn.j
    metnrmlem.1
    metnrmlem.2
    metnrmlem.3
    metnrmlem.4
    metnrmlem1
    @40
    @18
    cxr
    wcel
    @31
    cxr
    wcel
    @46
    cxr
    wcel
    #
    @76
    @72
    @73
    wa
    @74
    wi
    @40
    @18
    @55
    rpxrd
    @40
    @31
    @58
    rpxrd
    @40
    @42
    @43
    @44
    @76
    @47
    @52
    @53
    @16
    @29
    cD
    cX
    xmetcl
    syl3anc
    #
    @77
    @18
    @31
    @46
    @46
    xle2add
    syl22anc
    mp2and
    @40
    c2
    @60
    cmul
    co
    #
    @59
    @67
    @70
    @40
    @59
    c2
    @40
    @59
    @40
    @18
    @31
    @62
    @63
    readdcld
    #
    recnd
    @64
    @65
    divcan2d
    @40
    c2
    cr
    wcel
    @60
    cr
    wcel
    @67
    @78
    wceq
    2re
    @40
    @59
    @79
    rehalfcld
    #
    c2
    @60
    rexmul
    sylancr
    @40
    @18
    cr
    wcel
    @31
    cr
    wcel
    @70
    @59
    wceq
    @62
    @63
    @18
    @31
    rexadd
    syl2anc
    3eqtr4d
    @40
    @76
    @68
    @71
    wceq
    @77
    @46
    x2times
    syl
    3brtr4d
    @40
    @60
    cxr
    wcel
    @76
    c2
    crp
    wcel
    #
    @66
    @69
    wb
    @40
    @60
    @80
    rexrd
    @77
    @81
    @40
    2rp
    a1i
    @60
    @46
    c2
    xlemul2
    syl3anc
    mpbird
    eqbrtrd
    cD
    @16
    @29
    @19
    @32
    cX
    bldisj
    syl33anc
    @34
    c0
    eqimss
    syl
    anassrs
    ralrimiva
    vt
    cT
    @34
    c0
    iunss
    sylibr
    syl5eqss
    ralrimiva
    vs
    cS
    @22
    c0
    iunss
    sylibr
    @23
    ss0
    syl
    syl5eq
    @12
    @2
    @3
    @5
    w3a
    @2
    @9
    cV
    @8
    cin
    #
    c0
    wceq
    #
    w3a
    vz
    vw
    cV
    cU
    cJ
    cJ
    @6
    cV
    wceq
    #
    @7
    @2
    @11
    @83
    @9
    @6
    cV
    cS
    sseq2
    @84
    @10
    @82
    c0
    @6
    cV
    @8
    ineq1
    eqeq1d
    3anbi13d
    @8
    cU
    wceq
    #
    @9
    @3
    @83
    @5
    @2
    @8
    cU
    cT
    sseq2
    @85
    @82
    @4
    c0
    @8
    cU
    cV
    ineq2
    eqeq1d
    3anbi23d
    rspc2ev
    syl113anc
end
