include "clmod.mm"
include "wcel.mm"
include "wa.mm"
include "cghm.mm"
include "co.mm"
include "wceq.mm"
include "cv.mm"
include "cfv.mm"
include "wral.mm"
include "w3a.mm"
include "clmhm.mm"
include "jca.mm"
include "ralrimivva.mm"
include "3jca.mm"
include "islmhm.mm"
include "sylanbrc.mm"

theorem islmhmd
  let wph: wff ph
  let vx: setvar x
  let vy: setvar y
  let cS: class S
  let cT: class T
  let c.x: class .x.
  let c.xp: class .X.
  let cF: class F
  let cJ: class J
  let cK: class K
  let cN: class N
  let cX: class X
  assume islmhmd.x: |- X = ( Base ` S )
  assume islmhmd.a: |- .x. = ( .s ` S )
  assume islmhmd.b: |- .X. = ( .s ` T )
  assume islmhmd.k: |- K = ( Scalar ` S )
  assume islmhmd.j: |- J = ( Scalar ` T )
  assume islmhmd.n: |- N = ( Base ` K )
  assume islmhmd.s: |- ( ph -> S e. LMod )
  assume islmhmd.t: |- ( ph -> T e. LMod )
  assume islmhmd.c: |- ( ph -> J = K )
  assume islmhmd.f: |- ( ph -> F e. ( S GrpHom T ) )
  assume islmhmd.l: |- ( ( ph /\ ( x e. N /\ y e. X ) ) -> ( F ` ( x .x. y ) ) = ( x .X. ( F ` y ) ) )

  disjoint ph x
  disjoint ph y
  disjoint x y
  disjoint F x
  disjoint F y
  disjoint S x
  disjoint S y
  disjoint T x
  disjoint T y
  disjoint X x
  disjoint X y
  disjoint J x
  disjoint J y
  disjoint N x
  disjoint N y
  disjoint K x
  disjoint K y
  assert |- ( ph -> F e. ( S LMHom T ) )

  proof
    wph
    cS
    clmod
    wcel
    #
    cT
    clmod
    wcel
    #
    wa
    cF
    cS
    cT
    cghm
    co
    wcel
    #
    cJ
    cK
    wceq
    #
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
    @4
    @5
    cF
    cfv
    c.xp
    co
    wceq
    #
    vy
    cX
    wral
    vx
    cN
    wral
    #
    w3a
    cF
    cS
    cT
    clmhm
    co
    wcel
    wph
    @0
    @1
    islmhmd.s
    islmhmd.t
    jca
    wph
    @2
    @3
    @7
    islmhmd.f
    islmhmd.c
    wph
    @6
    vx
    vy
    cN
    cX
    islmhmd.l
    ralrimivva
    3jca
    vx
    vy
    cN
    cS
    cT
    c.x
    c.xp
    cX
    cF
    cK
    cJ
    islmhmd.k
    islmhmd.j
    islmhmd.n
    islmhmd.x
    islmhmd.a
    islmhmd.b
    islmhm
    sylanbrc
end
