include "wcel.mm"
include "cv.mm"
include "co.mm"
include "wceq.mm"
include "wral.mm"
include "w3a.mm"
include "wne.mm"
include "wa.mm"
include "cfv.mm"
include "simpr3.mm"
include "simpl3.mm"
include "wi.mm"
include "neeq2.mm"
include "oveq1.mm"
include "eqeq2d.mm"
include "ralbidv.mm"
include "anbi12d.mm"
include "imbi1d.mm"
include "simpl2.mm"
include "simpr1.mm"
include "simpl1.mm"
include "syl.mm"
include "oveq.mm"
include "eqeq12d.mm"
include "anbi2d.mm"
include "fveq2.mm"
include "eqeq1d.mm"
include "imbi12d.mm"
include "neeq1.mm"
include "rspc2va.mm"
include "syl21anc.mm"
include "simpr2.mm"
include "rspcdva.mm"
include "mp2and.mm"

theorem mdetunilem1
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
  let cH: class H
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
  disjoint H x
  disjoint H y
  disjoint H z
  disjoint H w
  assert |- ( ( ( ph /\ E e. B /\ A. w e. N ( F E w ) = ( G E w ) ) /\ ( F e. N /\ G e. N /\ F =/= G ) ) -> ( D ` E ) = .0. )

  proof
    wph
    cE
    cB
    wcel
    #
    cF
    vw
    cv
    #
    cE
    co
    #
    cG
    @1
    cE
    co
    #
    wceq
    #
    vw
    cN
    wral
    #
    w3a
    #
    cF
    cN
    wcel
    #
    cG
    cN
    wcel
    #
    cF
    cG
    wne
    #
    w3a
    #
    wa
    #
    @9
    @5
    cE
    cD
    cfv
    #
    c.0
    wceq
    #
    @6
    @7
    @8
    @9
    simpr3
    wph
    @0
    @5
    @10
    simpl3
    @11
    cF
    vz
    cv
    #
    wne
    #
    @2
    @14
    @1
    cE
    co
    #
    wceq
    #
    vw
    cN
    wral
    #
    wa
    #
    @13
    wi
    #
    @9
    @5
    wa
    #
    @13
    wi
    vz
    cN
    cG
    @14
    cG
    wceq
    #
    @19
    @21
    @13
    @22
    @15
    @9
    @18
    @5
    @14
    cG
    cF
    neeq2
    @22
    @17
    @4
    vw
    cN
    @22
    @16
    @3
    @2
    @14
    cG
    @1
    cE
    oveq1
    eqeq2d
    ralbidv
    anbi12d
    imbi1d
    @11
    @0
    @7
    vy
    cv
    #
    @14
    wne
    #
    @23
    @1
    vx
    cv
    #
    co
    #
    @14
    @1
    @25
    co
    #
    wceq
    #
    vw
    cN
    wral
    #
    wa
    #
    @25
    cD
    cfv
    #
    c.0
    wceq
    #
    wi
    #
    vz
    cN
    wral
    #
    vy
    cN
    wral
    vx
    cB
    wral
    #
    @20
    vz
    cN
    wral
    #
    wph
    @0
    @5
    @10
    simpl2
    @6
    @7
    @8
    @9
    simpr1
    @11
    wph
    @35
    wph
    @0
    @5
    @10
    simpl1
    mdetuni.al
    syl
    @34
    @36
    @24
    @23
    @1
    cE
    co
    #
    @16
    wceq
    #
    vw
    cN
    wral
    #
    wa
    #
    @13
    wi
    #
    vz
    cN
    wral
    vx
    vy
    cE
    cF
    cB
    cN
    @25
    cE
    wceq
    #
    @33
    @41
    vz
    cN
    @42
    @30
    @40
    @32
    @13
    @42
    @29
    @39
    @24
    @42
    @28
    @38
    vw
    cN
    @42
    @26
    @37
    @27
    @16
    @23
    @1
    @25
    cE
    oveq
    @14
    @1
    @25
    cE
    oveq
    eqeq12d
    ralbidv
    anbi2d
    @42
    @31
    @12
    c.0
    @25
    cE
    cD
    fveq2
    eqeq1d
    imbi12d
    ralbidv
    @23
    cF
    wceq
    #
    @41
    @20
    vz
    cN
    @43
    @40
    @19
    @13
    @43
    @24
    @15
    @39
    @18
    @23
    cF
    @14
    neeq1
    @43
    @38
    @17
    vw
    cN
    @43
    @37
    @2
    @16
    @23
    cF
    @1
    cE
    oveq1
    eqeq1d
    ralbidv
    anbi12d
    imbi1d
    ralbidv
    rspc2va
    syl21anc
    @6
    @7
    @8
    @9
    simpr2
    rspcdva
    mp2and
end
