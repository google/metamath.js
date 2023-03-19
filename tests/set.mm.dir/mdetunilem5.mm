include "cv.mm"
include "wceq.mm"
include "co.mm"
include "cif.mm"
include "cmpt2.mm"
include "wcel.mm"
include "csn.mm"
include "cxp.mm"
include "cres.mm"
include "cof.mm"
include "cdif.mm"
include "cfv.mm"
include "crg.mm"
include "cfn.mm"
include "syl.mm"
include "w3a.mm"
include "3ad2ant1.mm"
include "simp1d.mm"
include "simp2d.mm"
include "ringacl.mm"
include "syl3anc.mm"
include "simp3d.mm"
include "ifcld.mm"
include "matbas2d.mm"
include "cvv.mm"
include "snex.mm"
include "a1i.mm"
include "wss.mm"
include "snssd.mm"
include "simp2.mm"
include "sseldd.mm"
include "syld3an2.mm"
include "eqidd.mm"
include "offval22.mm"
include "eqcomd.mm"
include "mpt2snif.mm"
include "oveq12i.mm"
include "3eqtr4g.mm"
include "ssid.mm"
include "resmpt2.mm"
include "sylancl.mm"
include "oveq12d.mm"
include "3eqtr4d.mm"
include "wn.mm"
include "wne.mm"
include "eldifsni.mm"
include "3ad2ant2.mm"
include "neneqd.mm"
include "iffalse.mm"
include "eqtr4d.mm"
include "mpt2eq3dva.mm"
include "difss.mm"
include "mp2an.mm"
include "mdetunilem3.mm"
include "syl332anc.mm"

theorem mdetunilem5
  let wph: wff ph
  let wps: wff ps
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let vw: setvar w
  let cA: class A
  let cB: class B
  let cD: class D
  let c.pl: class .+
  let cR: class R
  let c.x: class .x.
  let c.1: class .1.
  let cE: class E
  let cF: class F
  let cG: class G
  let cH: class H
  let cK: class K
  let cN: class N
  let c.0: class .0.
  let va: setvar a
  let vb: setvar b
  let vc: setvar c
  let vd: setvar d
  let ve: setvar e
  let vf: setvar f
  let cY: class Y
  assume mdetuni.a: |- A = ( N Mat R )
  assume mdetuni.b: |- B = ( Base ` A )
  assume mdetuni.k: |- K = ( Base ` R )
  assume mdetuni.0g: |- .0. = ( 0g ` R )
  assume mdetuni.1r: |- .1. = ( 1r ` R )
  assume mdetuni.pg: |- .+ = ( +g ` R )
  assume mdetuni.tg: |- .x. = ( .r ` R )
  assume mdetuni.n: |- ( ph -> N e. Fin )
  assume mdetuni.r: |- ( ph -> R e. Ring )
  assume mdetuni.ff: |- ( ph -> D : B --> K )
  assume mdetuni.al: |- ( ph -> A. x e. B A. y e. N A. z e. N ( ( y =/= z /\ A. w e. N ( y x w ) = ( z x w ) ) -> ( D ` x ) = .0. ) )
  assume mdetuni.li: |- ( ph -> A. x e. B A. y e. B A. z e. B A. w e. N ( ( ( x |` ( { w } X. N ) ) = ( ( y |` ( { w } X. N ) ) oF .+ ( z |` ( { w } X. N ) ) ) /\ ( x |` ( ( N \ { w } ) X. N ) ) = ( y |` ( ( N \ { w } ) X. N ) ) /\ ( x |` ( ( N \ { w } ) X. N ) ) = ( z |` ( ( N \ { w } ) X. N ) ) ) -> ( D ` x ) = ( ( D ` y ) .+ ( D ` z ) ) ) )
  assume mdetuni.sc: |- ( ph -> A. x e. B A. y e. K A. z e. B A. w e. N ( ( ( x |` ( { w } X. N ) ) = ( ( ( { w } X. N ) X. { y } ) oF .x. ( z |` ( { w } X. N ) ) ) /\ ( x |` ( ( N \ { w } ) X. N ) ) = ( z |` ( ( N \ { w } ) X. N ) ) ) -> ( D ` x ) = ( y .x. ( D ` z ) ) ) )
  assume mdetunilem5.ph: |- ( ps -> ph )
  assume mdetunilem5.e: |- ( ps -> E e. N )
  assume mdetunilem5.fgh: |- ( ( ps /\ a e. N /\ b e. N ) -> ( F e. K /\ G e. K /\ H e. K ) )

  disjoint a ps
  disjoint b ps
  disjoint ps x
  disjoint ps y
  disjoint ps z
  disjoint ps w
  disjoint a b
  disjoint a x
  disjoint a y
  disjoint a z
  disjoint a w
  disjoint b x
  disjoint b y
  disjoint b z
  disjoint b w
  disjoint x y
  disjoint x z
  disjoint w x
  disjoint y z
  disjoint w y
  disjoint w z
  disjoint E a
  disjoint E b
  disjoint ph x
  disjoint ph y
  disjoint ph z
  disjoint ph w
  disjoint a ph
  disjoint b ph
  disjoint x y
  disjoint x z
  disjoint w x
  disjoint a x
  disjoint b x
  disjoint y z
  disjoint w y
  disjoint a y
  disjoint b y
  disjoint w z
  disjoint a z
  disjoint b z
  disjoint a w
  disjoint b w
  disjoint a b
  disjoint B x
  disjoint B y
  disjoint B z
  disjoint B w
  disjoint B a
  disjoint B b
  disjoint K x
  disjoint K y
  disjoint K z
  disjoint K w
  disjoint K a
  disjoint K b
  disjoint N x
  disjoint N y
  disjoint N z
  disjoint N w
  disjoint N a
  disjoint N b
  disjoint D x
  disjoint D y
  disjoint D z
  disjoint D w
  disjoint D a
  disjoint D b
  disjoint .x. x
  disjoint .x. y
  disjoint .x. z
  disjoint .x. w
  disjoint .+ a
  disjoint .+ b
  disjoint .+ x
  disjoint .+ y
  disjoint .+ z
  disjoint .+ w
  disjoint .0. a
  disjoint .0. b
  disjoint .0. x
  disjoint .0. y
  disjoint .0. z
  disjoint .0. w
  disjoint .1. a
  disjoint .1. b
  disjoint .1. x
  disjoint .1. y
  disjoint .1. z
  disjoint .1. w
  disjoint R x
  disjoint R y
  disjoint R z
  disjoint R w
  disjoint A a
  disjoint A b
  disjoint A x
  disjoint A y
  disjoint A z
  disjoint A w
  disjoint E x
  disjoint E y
  disjoint E z
  disjoint E w
  disjoint F x
  disjoint F y
  disjoint F z
  disjoint F w
  disjoint G x
  disjoint G y
  disjoint G z
  disjoint G w
  disjoint H x
  disjoint H y
  disjoint H z
  disjoint H w
  disjoint c ph
  disjoint d ph
  disjoint e ph
  disjoint f ph
  disjoint c x
  disjoint d x
  disjoint e x
  disjoint f x
  disjoint c y
  disjoint d y
  disjoint e y
  disjoint f y
  disjoint c z
  disjoint d z
  disjoint e z
  disjoint f z
  disjoint c w
  disjoint d w
  disjoint e w
  disjoint f w
  disjoint a c
  disjoint a d
  disjoint a e
  disjoint a f
  disjoint b c
  disjoint b d
  disjoint b e
  disjoint b f
  disjoint c d
  disjoint c e
  disjoint c f
  disjoint d e
  disjoint d f
  disjoint e f
  disjoint B c
  disjoint B d
  disjoint B e
  disjoint B f
  disjoint K c
  disjoint K d
  disjoint K e
  disjoint K f
  disjoint N c
  disjoint N d
  disjoint N e
  disjoint N f
  disjoint D c
  disjoint D d
  disjoint D e
  disjoint D f
  disjoint Y a
  disjoint Y b
  disjoint Y c
  disjoint Y d
  disjoint Y e
  disjoint Y f
  disjoint .x. e
  disjoint .+ e
  disjoint .0. c
  disjoint .0. d
  disjoint .0. e
  disjoint .1. c
  disjoint .1. d
  disjoint .1. e
  disjoint R e
  disjoint A c
  disjoint A d
  assert |- ( ps -> ( D ` ( a e. N , b e. N |-> if ( a = E , ( F .+ G ) , H ) ) ) = ( ( D ` ( a e. N , b e. N |-> if ( a = E , F , H ) ) ) .+ ( D ` ( a e. N , b e. N |-> if ( a = E , G , H ) ) ) ) )

  proof
    wps
    wph
    va
    vb
    cN
    cN
    va
    cv
    #
    cE
    wceq
    #
    cF
    cG
    c.pl
    co
    #
    cH
    cif
    #
    cmpt2
    #
    cB
    wcel
    va
    vb
    cN
    cN
    @1
    cF
    cH
    cif
    #
    cmpt2
    #
    cB
    wcel
    va
    vb
    cN
    cN
    @1
    cG
    cH
    cif
    #
    cmpt2
    #
    cB
    wcel
    cE
    cN
    wcel
    @4
    cE
    csn
    #
    cN
    cxp
    #
    cres
    #
    @6
    @10
    cres
    #
    @8
    @10
    cres
    #
    c.pl
    cof
    #
    co
    #
    wceq
    @4
    cN
    @9
    cdif
    #
    cN
    cxp
    #
    cres
    #
    @6
    @17
    cres
    #
    wceq
    @18
    @8
    @17
    cres
    #
    wceq
    @4
    cD
    cfv
    @6
    cD
    cfv
    @8
    cD
    cfv
    c.pl
    co
    wceq
    mdetunilem5.ph
    wps
    va
    vb
    cA
    cB
    @3
    cR
    cK
    cN
    crg
    mdetuni.a
    mdetuni.k
    mdetuni.b
    wps
    wph
    cN
    cfn
    wcel
    mdetunilem5.ph
    mdetuni.n
    syl
    #
    wps
    wph
    cR
    crg
    wcel
    #
    mdetunilem5.ph
    mdetuni.r
    syl
    #
    wps
    @0
    cN
    wcel
    #
    vb
    cv
    cN
    wcel
    #
    w3a
    #
    @1
    @2
    cH
    cK
    @26
    @22
    cF
    cK
    wcel
    #
    cG
    cK
    wcel
    #
    @2
    cK
    wcel
    wps
    @24
    @22
    @25
    @23
    3ad2ant1
    @26
    @27
    @28
    cH
    cK
    wcel
    #
    mdetunilem5.fgh
    simp1d
    #
    @26
    @27
    @28
    @29
    mdetunilem5.fgh
    simp2d
    #
    cK
    c.pl
    cR
    cF
    cG
    mdetuni.k
    mdetuni.pg
    ringacl
    syl3anc
    @26
    @27
    @28
    @29
    mdetunilem5.fgh
    simp3d
    #
    ifcld
    matbas2d
    wps
    va
    vb
    cA
    cB
    @5
    cR
    cK
    cN
    crg
    mdetuni.a
    mdetuni.k
    mdetuni.b
    @21
    @23
    @26
    @1
    cF
    cH
    cK
    @30
    @32
    ifcld
    matbas2d
    wps
    va
    vb
    cA
    cB
    @7
    cR
    cK
    cN
    crg
    mdetuni.a
    mdetuni.k
    mdetuni.b
    @21
    @23
    @26
    @1
    cG
    cH
    cK
    @31
    @32
    ifcld
    matbas2d
    mdetunilem5.e
    wps
    va
    vb
    @9
    cN
    @3
    cmpt2
    #
    va
    vb
    @9
    cN
    @5
    cmpt2
    #
    va
    vb
    @9
    cN
    @7
    cmpt2
    #
    @14
    co
    #
    @11
    @15
    wps
    va
    vb
    @9
    cN
    @2
    cmpt2
    #
    va
    vb
    @9
    cN
    cF
    cmpt2
    #
    va
    vb
    @9
    cN
    cG
    cmpt2
    #
    @14
    co
    #
    @33
    @36
    wps
    @40
    @37
    wps
    va
    vb
    @9
    cN
    cF
    cG
    c.pl
    @38
    @39
    cvv
    cfn
    cK
    cK
    @9
    cvv
    wcel
    wps
    cE
    snex
    a1i
    @21
    wps
    @24
    @0
    @9
    wcel
    #
    @25
    @27
    wps
    @41
    @25
    w3a
    @9
    cN
    @0
    wps
    @41
    @9
    cN
    wss
    #
    @25
    wps
    cE
    cN
    mdetunilem5.e
    snssd
    #
    3ad2ant1
    wps
    @41
    @25
    simp2
    sseldd
    #
    @30
    syld3an2
    wps
    @24
    @41
    @25
    @28
    @44
    @31
    syld3an2
    wps
    @38
    eqidd
    wps
    @39
    eqidd
    offval22
    eqcomd
    cN
    @2
    cH
    va
    vb
    cE
    mpt2snif
    @34
    @38
    @35
    @39
    @14
    cN
    cF
    cH
    va
    vb
    cE
    mpt2snif
    cN
    cG
    cH
    va
    vb
    cE
    mpt2snif
    oveq12i
    3eqtr4g
    wps
    @42
    cN
    cN
    wss
    #
    @11
    @33
    wceq
    @43
    cN
    ssid
    #
    va
    vb
    cN
    cN
    @9
    cN
    @3
    resmpt2
    sylancl
    wps
    @12
    @34
    @13
    @35
    @14
    wps
    @42
    @45
    @12
    @34
    wceq
    @43
    @46
    va
    vb
    cN
    cN
    @9
    cN
    @5
    resmpt2
    sylancl
    wps
    @42
    @45
    @13
    @35
    wceq
    @43
    @46
    va
    vb
    cN
    cN
    @9
    cN
    @7
    resmpt2
    sylancl
    oveq12d
    3eqtr4d
    wps
    va
    vb
    @16
    cN
    @3
    cmpt2
    #
    va
    vb
    @16
    cN
    @5
    cmpt2
    #
    @18
    @19
    wps
    va
    vb
    @16
    cN
    @3
    @5
    wps
    @0
    @16
    wcel
    #
    @25
    w3a
    #
    @1
    wn
    #
    @3
    @5
    wceq
    @50
    @0
    cE
    @49
    wps
    @0
    cE
    wne
    @25
    @0
    cN
    cE
    eldifsni
    3ad2ant2
    neneqd
    #
    @51
    @3
    cH
    @5
    @1
    @2
    cH
    iffalse
    #
    @1
    cF
    cH
    iffalse
    eqtr4d
    syl
    mpt2eq3dva
    @16
    cN
    wss
    #
    @45
    @18
    @47
    wceq
    cN
    @9
    difss
    #
    @46
    va
    vb
    cN
    cN
    @16
    cN
    @3
    resmpt2
    mp2an
    #
    @54
    @45
    @19
    @48
    wceq
    @55
    @46
    va
    vb
    cN
    cN
    @16
    cN
    @5
    resmpt2
    mp2an
    3eqtr4g
    wps
    @47
    va
    vb
    @16
    cN
    @7
    cmpt2
    #
    @18
    @20
    wps
    va
    vb
    @16
    cN
    @3
    @7
    @50
    @51
    @3
    @7
    wceq
    @52
    @51
    @3
    cH
    @7
    @53
    @1
    cG
    cH
    iffalse
    eqtr4d
    syl
    mpt2eq3dva
    @56
    @54
    @45
    @20
    @57
    wceq
    @55
    @46
    va
    vb
    cN
    cN
    @16
    cN
    @7
    resmpt2
    mp2an
    3eqtr4g
    wph
    vx
    vy
    vz
    vw
    cA
    cB
    cD
    c.pl
    cR
    c.x
    c.1
    @4
    @6
    @8
    cE
    cK
    cN
    c.0
    mdetuni.a
    mdetuni.b
    mdetuni.k
    mdetuni.0g
    mdetuni.1r
    mdetuni.pg
    mdetuni.tg
    mdetuni.n
    mdetuni.r
    mdetuni.ff
    mdetuni.al
    mdetuni.li
    mdetuni.sc
    mdetunilem3
    syl332anc
end
