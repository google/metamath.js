include "wcel.mm"
include "w3a.mm"
include "csn.mm"
include "cxp.mm"
include "cres.mm"
include "cof.mm"
include "co.mm"
include "wceq.mm"
include "cdif.mm"
include "cfv.mm"
include "simp32.mm"
include "simp33.mm"
include "wa.mm"
include "wi.mm"
include "simp1.mm"
include "cv.mm"
include "wral.mm"
include "simp23.mm"
include "simp3.mm"
include "simp21.mm"
include "simp22.mm"
include "3ad2ant1.mm"
include "reseq1.mm"
include "eqeq1d.mm"
include "anbi12d.mm"
include "fveq2.mm"
include "imbi12d.mm"
include "2ralbidv.mm"
include "sneq.mm"
include "xpeq2d.mm"
include "oveq1d.mm"
include "eqeq2d.mm"
include "anbi1d.mm"
include "oveq1.mm"
include "rspc2va.mm"
include "syl21anc.mm"
include "oveq2d.mm"
include "xpeq1d.mm"
include "reseq2d.mm"
include "oveq12d.mm"
include "eqeq12d.mm"
include "difeq2d.mm"
include "imbi1d.mm"
include "syl3an3.mm"
include "mp2and.mm"

theorem mdetunilem4
  let wph: wff ph
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

  disjoint ph x
  disjoint ph y
  disjoint ph z
  disjoint ph w
  disjoint x y
  disjoint x z
  disjoint w x
  disjoint y z
  disjoint w y
  disjoint w z
  disjoint B x
  disjoint B y
  disjoint B z
  disjoint B w
  disjoint K x
  disjoint K y
  disjoint K z
  disjoint K w
  disjoint N x
  disjoint N y
  disjoint N z
  disjoint N w
  disjoint D x
  disjoint D y
  disjoint D z
  disjoint D w
  disjoint .x. x
  disjoint .x. y
  disjoint .x. z
  disjoint .x. w
  disjoint .+ x
  disjoint .+ y
  disjoint .+ z
  disjoint .+ w
  disjoint .0. x
  disjoint .0. y
  disjoint .0. z
  disjoint .0. w
  disjoint .1. x
  disjoint .1. y
  disjoint .1. z
  disjoint .1. w
  disjoint R x
  disjoint R y
  disjoint R z
  disjoint R w
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
  disjoint a ph
  disjoint b ph
  disjoint c ph
  disjoint d ph
  disjoint e ph
  disjoint f ph
  disjoint a x
  disjoint b x
  disjoint c x
  disjoint d x
  disjoint e x
  disjoint f x
  disjoint a y
  disjoint b y
  disjoint c y
  disjoint d y
  disjoint e y
  disjoint f y
  disjoint a z
  disjoint b z
  disjoint c z
  disjoint d z
  disjoint e z
  disjoint f z
  disjoint a w
  disjoint b w
  disjoint c w
  disjoint d w
  disjoint e w
  disjoint f w
  disjoint a b
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
  disjoint B a
  disjoint B b
  disjoint B c
  disjoint B d
  disjoint B e
  disjoint B f
  disjoint K a
  disjoint K b
  disjoint K c
  disjoint K d
  disjoint K e
  disjoint K f
  disjoint N a
  disjoint N b
  disjoint N c
  disjoint N d
  disjoint N e
  disjoint N f
  disjoint D a
  disjoint D b
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
  disjoint .+ a
  disjoint .+ b
  disjoint .+ e
  disjoint .0. a
  disjoint .0. b
  disjoint .0. c
  disjoint .0. d
  disjoint .0. e
  disjoint .1. a
  disjoint .1. b
  disjoint .1. c
  disjoint .1. d
  disjoint .1. e
  disjoint R e
  disjoint A a
  disjoint A b
  disjoint A c
  disjoint A d
  assert |- ( ( ph /\ ( E e. B /\ F e. K /\ G e. B ) /\ ( H e. N /\ ( E |` ( { H } X. N ) ) = ( ( ( { H } X. N ) X. { F } ) oF .x. ( G |` ( { H } X. N ) ) ) /\ ( E |` ( ( N \ { H } ) X. N ) ) = ( G |` ( ( N \ { H } ) X. N ) ) ) ) -> ( D ` E ) = ( F .x. ( D ` G ) ) )

  proof
    wph
    cE
    cB
    wcel
    #
    cF
    cK
    wcel
    #
    cG
    cB
    wcel
    #
    w3a
    #
    cH
    cN
    wcel
    #
    cE
    cH
    csn
    #
    cN
    cxp
    #
    cres
    #
    @6
    cF
    csn
    #
    cxp
    #
    cG
    @6
    cres
    #
    c.x
    cof
    #
    co
    #
    wceq
    #
    cE
    cN
    @5
    cdif
    #
    cN
    cxp
    #
    cres
    #
    cG
    @15
    cres
    #
    wceq
    #
    w3a
    #
    w3a
    @13
    @18
    cE
    cD
    cfv
    #
    cF
    cG
    cD
    cfv
    #
    c.x
    co
    #
    wceq
    #
    wph
    @3
    @4
    @13
    @18
    simp32
    wph
    @3
    @4
    @13
    @18
    simp33
    @19
    wph
    @3
    @4
    @13
    @18
    wa
    #
    @23
    wi
    #
    @4
    @13
    @18
    simp1
    wph
    @3
    @4
    w3a
    #
    @2
    @4
    cE
    vw
    cv
    #
    csn
    #
    cN
    cxp
    #
    cres
    #
    @29
    @8
    cxp
    #
    vz
    cv
    #
    @29
    cres
    #
    @11
    co
    #
    wceq
    #
    cE
    cN
    @28
    cdif
    #
    cN
    cxp
    #
    cres
    #
    @32
    @37
    cres
    #
    wceq
    #
    wa
    #
    @20
    cF
    @32
    cD
    cfv
    #
    c.x
    co
    #
    wceq
    #
    wi
    #
    vw
    cN
    wral
    vz
    cB
    wral
    #
    @25
    wph
    @0
    @1
    @2
    @4
    simp23
    wph
    @3
    @4
    simp3
    @26
    @0
    @1
    vx
    cv
    #
    @29
    cres
    #
    @29
    vy
    cv
    #
    csn
    #
    cxp
    #
    @33
    @11
    co
    #
    wceq
    #
    @47
    @37
    cres
    #
    @39
    wceq
    #
    wa
    #
    @47
    cD
    cfv
    #
    @49
    @42
    c.x
    co
    #
    wceq
    #
    wi
    #
    vw
    cN
    wral
    vz
    cB
    wral
    #
    vy
    cK
    wral
    vx
    cB
    wral
    #
    @46
    wph
    @0
    @1
    @2
    @4
    simp21
    wph
    @0
    @1
    @2
    @4
    simp22
    wph
    @3
    @62
    @4
    mdetuni.sc
    3ad2ant1
    @61
    @46
    @30
    @52
    wceq
    #
    @40
    wa
    #
    @20
    @58
    wceq
    #
    wi
    #
    vw
    cN
    wral
    vz
    cB
    wral
    vx
    vy
    cE
    cF
    cB
    cK
    @47
    cE
    wceq
    #
    @60
    @66
    vz
    vw
    cB
    cN
    @67
    @56
    @64
    @59
    @65
    @67
    @53
    @63
    @55
    @40
    @67
    @48
    @30
    @52
    @47
    cE
    @29
    reseq1
    eqeq1d
    @67
    @54
    @38
    @39
    @47
    cE
    @37
    reseq1
    eqeq1d
    anbi12d
    @67
    @57
    @20
    @58
    @47
    cE
    cD
    fveq2
    eqeq1d
    imbi12d
    2ralbidv
    @49
    cF
    wceq
    #
    @66
    @45
    vz
    vw
    cB
    cN
    @68
    @64
    @41
    @65
    @44
    @68
    @63
    @35
    @40
    @68
    @52
    @34
    @30
    @68
    @51
    @31
    @33
    @11
    @68
    @50
    @8
    @29
    @49
    cF
    sneq
    xpeq2d
    oveq1d
    eqeq2d
    anbi1d
    @68
    @58
    @43
    @20
    @49
    cF
    @42
    c.x
    oveq1
    eqeq2d
    imbi12d
    2ralbidv
    rspc2va
    syl21anc
    @45
    @25
    @30
    @31
    cG
    @29
    cres
    #
    @11
    co
    #
    wceq
    #
    @38
    cG
    @37
    cres
    #
    wceq
    #
    wa
    #
    @23
    wi
    vz
    vw
    cG
    cH
    cB
    cN
    @32
    cG
    wceq
    #
    @41
    @74
    @44
    @23
    @75
    @35
    @71
    @40
    @73
    @75
    @34
    @70
    @30
    @75
    @33
    @69
    @31
    @11
    @32
    cG
    @29
    reseq1
    oveq2d
    eqeq2d
    @75
    @39
    @72
    @38
    @32
    cG
    @37
    reseq1
    eqeq2d
    anbi12d
    @75
    @43
    @22
    @20
    @75
    @42
    @21
    cF
    c.x
    @32
    cG
    cD
    fveq2
    oveq2d
    eqeq2d
    imbi12d
    @27
    cH
    wceq
    #
    @74
    @24
    @23
    @76
    @71
    @13
    @73
    @18
    @76
    @30
    @7
    @70
    @12
    @76
    @29
    @6
    cE
    @76
    @28
    @5
    cN
    @27
    cH
    sneq
    #
    xpeq1d
    #
    reseq2d
    @76
    @31
    @9
    @69
    @10
    @11
    @76
    @29
    @6
    @8
    @78
    xpeq1d
    @76
    @29
    @6
    cG
    @78
    reseq2d
    oveq12d
    eqeq12d
    @76
    @38
    @16
    @72
    @17
    @76
    @37
    @15
    cE
    @76
    @36
    @14
    cN
    @76
    @28
    @5
    cN
    @77
    difeq2d
    xpeq1d
    #
    reseq2d
    @76
    @37
    @15
    cG
    @79
    reseq2d
    eqeq12d
    anbi12d
    imbi1d
    rspc2va
    syl21anc
    syl3an3
    mp2and
end
