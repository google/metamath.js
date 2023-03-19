include "wcel.mm"
include "w3a.mm"
include "csn.mm"
include "cxp.mm"
include "cres.mm"
include "cof.mm"
include "co.mm"
include "wceq.mm"
include "cdif.mm"
include "wa.mm"
include "cfv.mm"
include "simp23.mm"
include "simp3l.mm"
include "simp3r.mm"
include "wi.mm"
include "cv.mm"
include "wral.mm"
include "simprl.mm"
include "simprr.mm"
include "simpl2.mm"
include "simpl3.mm"
include "simpl1.mm"
include "syl.mm"
include "reseq1.mm"
include "eqeq1d.mm"
include "3anbi123d.mm"
include "fveq2.mm"
include "imbi12d.mm"
include "2ralbidv.mm"
include "oveq1d.mm"
include "eqeq2d.mm"
include "3anbi12d.mm"
include "rspc2va.mm"
include "syl21anc.mm"
include "oveq2d.mm"
include "3anbi13d.mm"
include "sneq.mm"
include "xpeq1d.mm"
include "reseq2d.mm"
include "oveq12d.mm"
include "eqeq12d.mm"
include "difeq2d.mm"
include "imbi1d.mm"
include "3adantr3.mm"
include "3adant3.mm"
include "mp3and.mm"

theorem mdetunilem3
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
  assert |- ( ( ( ph /\ E e. B /\ F e. B ) /\ ( G e. B /\ H e. N /\ ( E |` ( { H } X. N ) ) = ( ( F |` ( { H } X. N ) ) oF .+ ( G |` ( { H } X. N ) ) ) ) /\ ( ( E |` ( ( N \ { H } ) X. N ) ) = ( F |` ( ( N \ { H } ) X. N ) ) /\ ( E |` ( ( N \ { H } ) X. N ) ) = ( G |` ( ( N \ { H } ) X. N ) ) ) ) -> ( D ` E ) = ( ( D ` F ) .+ ( D ` G ) ) )

  proof
    wph
    cE
    cB
    wcel
    #
    cF
    cB
    wcel
    #
    w3a
    #
    cG
    cB
    wcel
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
    cF
    @6
    cres
    #
    cG
    @6
    cres
    #
    c.pl
    cof
    #
    co
    #
    wceq
    #
    w3a
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
    cF
    @15
    cres
    #
    wceq
    #
    @16
    cG
    @15
    cres
    #
    wceq
    #
    wa
    #
    w3a
    @12
    @18
    @20
    cE
    cD
    cfv
    #
    cF
    cD
    cfv
    #
    cG
    cD
    cfv
    #
    c.pl
    co
    #
    wceq
    #
    @2
    @3
    @4
    @12
    @21
    simp23
    @2
    @13
    @18
    @20
    simp3l
    @2
    @13
    @18
    @20
    simp3r
    @2
    @13
    @12
    @18
    @20
    w3a
    #
    @26
    wi
    #
    @21
    @2
    @3
    @4
    @28
    @12
    @2
    @3
    @4
    wa
    #
    wa
    #
    @3
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
    cF
    @33
    cres
    #
    vz
    cv
    #
    @33
    cres
    #
    @10
    co
    #
    wceq
    #
    cE
    cN
    @32
    cdif
    #
    cN
    cxp
    #
    cres
    #
    cF
    @41
    cres
    #
    wceq
    #
    @42
    @36
    @41
    cres
    #
    wceq
    #
    w3a
    #
    @22
    @23
    @36
    cD
    cfv
    #
    c.pl
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
    @28
    @2
    @3
    @4
    simprl
    @2
    @3
    @4
    simprr
    @30
    @0
    @1
    vx
    cv
    #
    @33
    cres
    #
    vy
    cv
    #
    @33
    cres
    #
    @37
    @10
    co
    #
    wceq
    #
    @53
    @41
    cres
    #
    @55
    @41
    cres
    #
    wceq
    #
    @59
    @45
    wceq
    #
    w3a
    #
    @53
    cD
    cfv
    #
    @55
    cD
    cfv
    #
    @48
    c.pl
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
    cB
    wral
    vx
    cB
    wral
    #
    @52
    wph
    @0
    @1
    @29
    simpl2
    wph
    @0
    @1
    @29
    simpl3
    @30
    wph
    @70
    wph
    @0
    @1
    @29
    simpl1
    mdetuni.li
    syl
    @69
    @52
    @34
    @57
    wceq
    #
    @42
    @60
    wceq
    #
    @46
    w3a
    #
    @22
    @66
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
    cB
    @53
    cE
    wceq
    #
    @68
    @75
    vz
    vw
    cB
    cN
    @76
    @63
    @73
    @67
    @74
    @76
    @58
    @71
    @61
    @72
    @62
    @46
    @76
    @54
    @34
    @57
    @53
    cE
    @33
    reseq1
    eqeq1d
    @76
    @59
    @42
    @60
    @53
    cE
    @41
    reseq1
    #
    eqeq1d
    @76
    @59
    @42
    @45
    @77
    eqeq1d
    3anbi123d
    @76
    @64
    @22
    @66
    @53
    cE
    cD
    fveq2
    eqeq1d
    imbi12d
    2ralbidv
    @55
    cF
    wceq
    #
    @75
    @51
    vz
    vw
    cB
    cN
    @78
    @73
    @47
    @74
    @50
    @78
    @71
    @39
    @72
    @44
    @46
    @78
    @57
    @38
    @34
    @78
    @56
    @35
    @37
    @10
    @55
    cF
    @33
    reseq1
    oveq1d
    eqeq2d
    @78
    @60
    @43
    @42
    @55
    cF
    @41
    reseq1
    eqeq2d
    3anbi12d
    @78
    @66
    @49
    @22
    @78
    @65
    @23
    @48
    c.pl
    @55
    cF
    cD
    fveq2
    oveq1d
    eqeq2d
    imbi12d
    2ralbidv
    rspc2va
    syl21anc
    @51
    @28
    @34
    @35
    cG
    @33
    cres
    #
    @10
    co
    #
    wceq
    #
    @44
    @42
    cG
    @41
    cres
    #
    wceq
    #
    w3a
    #
    @26
    wi
    vz
    vw
    cG
    cH
    cB
    cN
    @36
    cG
    wceq
    #
    @47
    @84
    @50
    @26
    @85
    @39
    @81
    @46
    @83
    @44
    @85
    @38
    @80
    @34
    @85
    @37
    @79
    @35
    @10
    @36
    cG
    @33
    reseq1
    oveq2d
    eqeq2d
    @85
    @45
    @82
    @42
    @36
    cG
    @41
    reseq1
    eqeq2d
    3anbi13d
    @85
    @49
    @25
    @22
    @85
    @48
    @24
    @23
    c.pl
    @36
    cG
    cD
    fveq2
    oveq2d
    eqeq2d
    imbi12d
    @31
    cH
    wceq
    #
    @84
    @27
    @26
    @86
    @81
    @12
    @44
    @18
    @83
    @20
    @86
    @34
    @7
    @80
    @11
    @86
    @33
    @6
    cE
    @86
    @32
    @5
    cN
    @31
    cH
    sneq
    #
    xpeq1d
    #
    reseq2d
    @86
    @35
    @8
    @79
    @9
    @10
    @86
    @33
    @6
    cF
    @88
    reseq2d
    @86
    @33
    @6
    cG
    @88
    reseq2d
    oveq12d
    eqeq12d
    @86
    @42
    @16
    @43
    @17
    @86
    @41
    @15
    cE
    @86
    @40
    @14
    cN
    @86
    @32
    @5
    cN
    @87
    difeq2d
    xpeq1d
    #
    reseq2d
    #
    @86
    @41
    @15
    cF
    @89
    reseq2d
    eqeq12d
    @86
    @42
    @16
    @82
    @19
    @90
    @86
    @41
    @15
    cG
    @89
    reseq2d
    eqeq12d
    3anbi123d
    imbi1d
    rspc2va
    syl21anc
    3adantr3
    3adant3
    mp3and
end
