include "crng.mm"
include "wcel.mm"
include "wa.mm"
include "cghm.mm"
include "co.mm"
include "cv.mm"
include "cfv.mm"
include "wceq.mm"
include "wral.mm"
include "crngh.mm"
include "jca.mm"
include "ralrimivva.mm"
include "isrnghm.mm"
include "sylanbrc.mm"

theorem isrnghm2d
  let wph: wff ph
  let vx: setvar x
  let vy: setvar y
  let cB: class B
  let cR: class R
  let cS: class S
  let c.x: class .x.
  let c.xp: class .X.
  let cF: class F
  let cC: class C
  let c.pl: class .+
  let c.pd: class .+^
  let vk: setvar k
  assume isrnghmd.b: |- B = ( Base ` R )
  assume isrnghmd.t: |- .x. = ( .r ` R )
  assume isrnghmd.u: |- .X. = ( .r ` S )
  assume isrnghmd.r: |- ( ph -> R e. Rng )
  assume isrnghmd.s: |- ( ph -> S e. Rng )
  assume isrnghmd.ht: |- ( ( ph /\ ( x e. B /\ y e. B ) ) -> ( F ` ( x .x. y ) ) = ( ( F ` x ) .X. ( F ` y ) ) )
  assume isrnghm2d.f: |- ( ph -> F e. ( R GrpHom S ) )

  disjoint ph x
  disjoint ph y
  disjoint x y
  disjoint B x
  disjoint B y
  disjoint F x
  disjoint F y
  disjoint R x
  disjoint R y
  disjoint S x
  disjoint S y
  disjoint C x
  disjoint C y
  disjoint .+ x
  disjoint .+ y
  disjoint .+^ x
  disjoint .+^ y
  disjoint k x
  assert |- ( ph -> F e. ( R RngHomo S ) )

  proof
    wph
    cR
    crng
    wcel
    #
    cS
    crng
    wcel
    #
    wa
    cF
    cR
    cS
    cghm
    co
    wcel
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
    @3
    cF
    cfv
    @4
    cF
    cfv
    c.xp
    co
    wceq
    #
    vy
    cB
    wral
    vx
    cB
    wral
    #
    wa
    cF
    cR
    cS
    crngh
    co
    wcel
    wph
    @0
    @1
    isrnghmd.r
    isrnghmd.s
    jca
    wph
    @2
    @6
    isrnghm2d.f
    wph
    @5
    vx
    vy
    cB
    cB
    isrnghmd.ht
    ralrimivva
    jca
    vx
    vy
    cB
    cR
    cS
    c.x
    cF
    c.xp
    isrnghmd.b
    isrnghmd.t
    isrnghmd.u
    isrnghm
    sylanbrc
end
