include "clmhm.mm"
include "co.mm"
include "wcel.mm"
include "clmod.mm"
include "wa.mm"
include "cghm.mm"
include "wceq.mm"
include "cv.mm"
include "cfv.mm"
include "wral.mm"
include "w3a.mm"
include "islmhm.mm"
include "baib.mm"

theorem islmhm3
  let vx: setvar x
  let vy: setvar y
  let cB: class B
  let cS: class S
  let cT: class T
  let c.x: class .x.
  let c.xp: class .X.
  let cE: class E
  let cF: class F
  let cK: class K
  let cL: class L
  let vf: setvar f
  let vs: setvar s
  let vt: setvar t
  let vw: setvar w
  let vg: setvar g
  assume islmhm.k: |- K = ( Scalar ` S )
  assume islmhm.l: |- L = ( Scalar ` T )
  assume islmhm.b: |- B = ( Base ` K )
  assume islmhm.e: |- E = ( Base ` S )
  assume islmhm.m: |- .x. = ( .s ` S )
  assume islmhm.n: |- .X. = ( .s ` T )

  disjoint B x
  disjoint E y
  disjoint x y
  disjoint S x
  disjoint S y
  disjoint F x
  disjoint F y
  disjoint T x
  disjoint T y
  disjoint f s
  disjoint f t
  disjoint f w
  disjoint f x
  disjoint B f
  disjoint s t
  disjoint s w
  disjoint s x
  disjoint B s
  disjoint t w
  disjoint t x
  disjoint B t
  disjoint w x
  disjoint B w
  disjoint f y
  disjoint E f
  disjoint s y
  disjoint E s
  disjoint t y
  disjoint E t
  disjoint w y
  disjoint E w
  disjoint K f
  disjoint K s
  disjoint K t
  disjoint K w
  disjoint S f
  disjoint S s
  disjoint S t
  disjoint S w
  disjoint F f
  disjoint f g
  disjoint T f
  disjoint g s
  disjoint g t
  disjoint g w
  disjoint g x
  disjoint g y
  disjoint T g
  disjoint T s
  disjoint T t
  disjoint T w
  disjoint .x. f
  disjoint .x. s
  disjoint .x. t
  disjoint .x. w
  disjoint .X. f
  disjoint .X. s
  disjoint .X. t
  disjoint .X. w
  disjoint L f
  disjoint L s
  disjoint L t
  disjoint L w
  assert |- ( ( S e. LMod /\ T e. LMod ) -> ( F e. ( S LMHom T ) <-> ( F e. ( S GrpHom T ) /\ L = K /\ A. x e. B A. y e. E ( F ` ( x .x. y ) ) = ( x .X. ( F ` y ) ) ) ) )

  proof
    cF
    cS
    cT
    clmhm
    co
    wcel
    cS
    clmod
    wcel
    cT
    clmod
    wcel
    wa
    cF
    cS
    cT
    cghm
    co
    wcel
    cL
    cK
    wceq
    vx
    cv
    #
    vy
    cv
    #
    c.x
    co
    cF
    cfv
    @0
    @1
    cF
    cfv
    c.xp
    co
    wceq
    vy
    cE
    wral
    vx
    cB
    wral
    w3a
    vx
    vy
    cB
    cS
    cT
    c.x
    c.xp
    cE
    cF
    cK
    cL
    islmhm.k
    islmhm.l
    islmhm.b
    islmhm.e
    islmhm.m
    islmhm.n
    islmhm
    baib
end
