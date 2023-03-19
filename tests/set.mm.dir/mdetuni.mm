include "cfv.mm"
include "cur.mm"
include "co.mm"
include "mdetuni0.mm"
include "oveq1d.mm"
include "crg.mm"
include "wcel.mm"
include "wceq.mm"
include "ccrg.mm"
include "mdetcl.mm"
include "syl2anc.mm"
include "ringlidm.mm"
include "3eqtrd.mm"

theorem mdetuni
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
  let cG: class G
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
  assume mdetuni.e: |- E = ( N maDet R )
  assume mdetuni.cr: |- ( ph -> R e. CRing )
  assume mdetuni.f: |- ( ph -> F e. B )
  assume mdetuni.no: |- ( ph -> ( D ` ( 1r ` A ) ) = .1. )

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
  disjoint G x
  disjoint G y
  disjoint G z
  disjoint G w
  disjoint H x
  disjoint H y
  disjoint H z
  disjoint H w
  disjoint R a
  disjoint R b
  disjoint R c
  disjoint R d
  disjoint .x. a
  disjoint .x. b
  disjoint .x. c
  disjoint .x. d
  disjoint E a
  disjoint E b
  disjoint E c
  disjoint E d
  disjoint E e
  disjoint F a
  disjoint A e
  disjoint .+ c
  disjoint .+ d
  assert |- ( ph -> ( D ` F ) = ( E ` F ) )

  proof
    wph
    cF
    cD
    cfv
    cA
    cur
    cfv
    cD
    cfv
    #
    cF
    cE
    cfv
    #
    c.x
    co
    c.1
    @1
    c.x
    co
    #
    @1
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
    cE
    cF
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
    mdetuni.e
    mdetuni.cr
    mdetuni.f
    mdetuni0
    wph
    @0
    c.1
    @1
    c.x
    mdetuni.no
    oveq1d
    wph
    cR
    crg
    wcel
    @1
    cK
    wcel
    #
    @2
    @1
    wceq
    mdetuni.r
    wph
    cR
    ccrg
    wcel
    cF
    cB
    wcel
    @3
    mdetuni.cr
    mdetuni.f
    cA
    cB
    cE
    cR
    cK
    cF
    cN
    mdetuni.e
    mdetuni.a
    mdetuni.b
    mdetuni.k
    mdetcl
    syl2anc
    cK
    cR
    c.x
    c.1
    @1
    mdetuni.k
    mdetuni.tg
    mdetuni.1r
    ringlidm
    syl2anc
    3eqtrd
end
