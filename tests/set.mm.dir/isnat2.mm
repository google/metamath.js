include "co.mm"
include "wcel.mm"
include "c1st.mm"
include "cfv.mm"
include "c2nd.mm"
include "cop.mm"
include "cv.mm"
include "cixp.mm"
include "wceq.mm"
include "wral.mm"
include "wa.mm"
include "cfunc.mm"
include "wrel.mm"
include "relfunc.mm"
include "1st2nd.mm"
include "sylancr.mm"
include "oveq12d.mm"
include "eleq2d.mm"
include "wbr.mm"
include "1st2ndbr.mm"
include "isnat.mm"
include "bitrd.mm"

theorem isnat2
  let wph: wff ph
  let vx: setvar x
  let vy: setvar y
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D
  let c.x: class .x.
  let vh: setvar h
  let cF: class F
  let cG: class G
  let cH: class H
  let cJ: class J
  let cN: class N
  let va: setvar a
  let vb: setvar b
  let vf: setvar f
  let vg: setvar g
  let vr: setvar r
  let vs: setvar s
  let vt: setvar t
  let vu: setvar u
  let vv: setvar v
  let cK: class K
  let cL: class L
  assume natfval.1: |- N = ( C Nat D )
  assume natfval.b: |- B = ( Base ` C )
  assume natfval.h: |- H = ( Hom ` C )
  assume natfval.j: |- J = ( Hom ` D )
  assume natfval.o: |- .x. = ( comp ` D )
  assume isnat2.f: |- ( ph -> F e. ( C Func D ) )
  assume isnat2.g: |- ( ph -> G e. ( C Func D ) )

  disjoint h x
  disjoint h y
  disjoint x y
  disjoint A h
  disjoint A x
  disjoint A y
  disjoint B x
  disjoint B y
  disjoint C h
  disjoint C x
  disjoint C y
  disjoint F h
  disjoint F x
  disjoint F y
  disjoint G h
  disjoint G x
  disjoint G y
  disjoint H h
  disjoint h ph
  disjoint ph x
  disjoint ph y
  disjoint D h
  disjoint D x
  disjoint D y
  disjoint a b
  disjoint a f
  disjoint a g
  disjoint a h
  disjoint a r
  disjoint a s
  disjoint a t
  disjoint a u
  disjoint a v
  disjoint a x
  disjoint a y
  disjoint b f
  disjoint b g
  disjoint b h
  disjoint b r
  disjoint b s
  disjoint b t
  disjoint b u
  disjoint b v
  disjoint b x
  disjoint b y
  disjoint f g
  disjoint f h
  disjoint f r
  disjoint f s
  disjoint f t
  disjoint f u
  disjoint f v
  disjoint f x
  disjoint f y
  disjoint g h
  disjoint g r
  disjoint g s
  disjoint g t
  disjoint g u
  disjoint g v
  disjoint g x
  disjoint g y
  disjoint h r
  disjoint h s
  disjoint h t
  disjoint h u
  disjoint h v
  disjoint r s
  disjoint r t
  disjoint r u
  disjoint r v
  disjoint r x
  disjoint r y
  disjoint s t
  disjoint s u
  disjoint s v
  disjoint s x
  disjoint s y
  disjoint t u
  disjoint t v
  disjoint t x
  disjoint t y
  disjoint u v
  disjoint u x
  disjoint u y
  disjoint v x
  disjoint v y
  disjoint A a
  disjoint B a
  disjoint B f
  disjoint B g
  disjoint B r
  disjoint B s
  disjoint B t
  disjoint B u
  disjoint C a
  disjoint C f
  disjoint C g
  disjoint C r
  disjoint C s
  disjoint C t
  disjoint C u
  disjoint F a
  disjoint F f
  disjoint F g
  disjoint F r
  disjoint F s
  disjoint J a
  disjoint J f
  disjoint J g
  disjoint J r
  disjoint J s
  disjoint J t
  disjoint J u
  disjoint G a
  disjoint G f
  disjoint G g
  disjoint G r
  disjoint G s
  disjoint H a
  disjoint H f
  disjoint H g
  disjoint H r
  disjoint H s
  disjoint H t
  disjoint H u
  disjoint a ph
  disjoint f ph
  disjoint g ph
  disjoint ph r
  disjoint ph s
  disjoint K a
  disjoint K f
  disjoint K g
  disjoint K h
  disjoint K r
  disjoint K s
  disjoint K x
  disjoint K y
  disjoint L a
  disjoint L f
  disjoint L g
  disjoint L h
  disjoint L r
  disjoint L s
  disjoint L x
  disjoint L y
  disjoint .x. a
  disjoint .x. f
  disjoint .x. g
  disjoint .x. r
  disjoint .x. s
  disjoint .x. t
  disjoint .x. u
  disjoint D a
  disjoint D f
  disjoint D g
  disjoint D r
  disjoint D s
  disjoint D t
  disjoint D u
  assert |- ( ph -> ( A e. ( F N G ) <-> ( A e. X_ x e. B ( ( ( 1st ` F ) ` x ) J ( ( 1st ` G ) ` x ) ) /\ A. x e. B A. y e. B A. h e. ( x H y ) ( ( A ` y ) ( <. ( ( 1st ` F ) ` x ) , ( ( 1st ` F ) ` y ) >. .x. ( ( 1st ` G ) ` y ) ) ( ( x ( 2nd ` F ) y ) ` h ) ) = ( ( ( x ( 2nd ` G ) y ) ` h ) ( <. ( ( 1st ` F ) ` x ) , ( ( 1st ` G ) ` x ) >. .x. ( ( 1st ` G ) ` y ) ) ( A ` x ) ) ) ) )

  proof
    wph
    cA
    cF
    cG
    cN
    co
    #
    wcel
    cA
    cF
    c1st
    cfv
    #
    cF
    c2nd
    cfv
    #
    cop
    #
    cG
    c1st
    cfv
    #
    cG
    c2nd
    cfv
    #
    cop
    #
    cN
    co
    #
    wcel
    cA
    vx
    cB
    vx
    cv
    #
    @1
    cfv
    #
    @8
    @4
    cfv
    #
    cJ
    co
    cixp
    wcel
    vy
    cv
    #
    cA
    cfv
    vh
    cv
    #
    @8
    @11
    @2
    co
    cfv
    @9
    @11
    @1
    cfv
    cop
    @11
    @4
    cfv
    #
    c.x
    co
    co
    @12
    @8
    @11
    @5
    co
    cfv
    @8
    cA
    cfv
    @9
    @10
    cop
    @13
    c.x
    co
    co
    wceq
    vh
    @8
    @11
    cH
    co
    wral
    vy
    cB
    wral
    vx
    cB
    wral
    wa
    wph
    @0
    @7
    cA
    wph
    cF
    @3
    cG
    @6
    cN
    wph
    cC
    cD
    cfunc
    co
    #
    wrel
    #
    cF
    @14
    wcel
    #
    cF
    @3
    wceq
    cC
    cD
    relfunc
    #
    isnat2.f
    cF
    @14
    1st2nd
    sylancr
    wph
    @15
    cG
    @14
    wcel
    #
    cG
    @6
    wceq
    @17
    isnat2.g
    cG
    @14
    1st2nd
    sylancr
    oveq12d
    eleq2d
    wph
    vx
    vy
    cA
    cB
    cC
    cD
    c.x
    vh
    @1
    @2
    cH
    cJ
    @4
    @5
    cN
    natfval.1
    natfval.b
    natfval.h
    natfval.j
    natfval.o
    wph
    @15
    @16
    @1
    @2
    @14
    wbr
    @17
    isnat2.f
    cF
    @14
    1st2ndbr
    sylancr
    wph
    @15
    @18
    @4
    @5
    @14
    wbr
    @17
    isnat2.g
    cG
    @14
    1st2ndbr
    sylancr
    isnat
    bitrd
end
