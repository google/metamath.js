include "cgrp.mm"
include "wcel.mm"
include "wa.mm"
include "wf.mm"
include "cv.mm"
include "co.mm"
include "cfv.mm"
include "wceq.mm"
include "wral.mm"
include "cghm.mm"
include "jca.mm"
include "ralrimivva.mm"
include "isghm.mm"
include "sylanbrc.mm"

theorem isghmd
  let wph: wff ph
  let vx: setvar x
  let vy: setvar y
  let c.pl: class .+
  let c.pd: class .+^
  let cS: class S
  let cT: class T
  let cF: class F
  let cX: class X
  let cY: class Y
  assume isghmd.x: |- X = ( Base ` S )
  assume isghmd.y: |- Y = ( Base ` T )
  assume isghmd.a: |- .+ = ( +g ` S )
  assume isghmd.b: |- .+^ = ( +g ` T )
  assume isghmd.s: |- ( ph -> S e. Grp )
  assume isghmd.t: |- ( ph -> T e. Grp )
  assume isghmd.f: |- ( ph -> F : X --> Y )
  assume isghmd.l: |- ( ( ph /\ ( x e. X /\ y e. X ) ) -> ( F ` ( x .+ y ) ) = ( ( F ` x ) .+^ ( F ` y ) ) )

  disjoint ph x
  disjoint ph y
  disjoint x y
  disjoint F x
  disjoint F y
  disjoint S x
  disjoint S y
  disjoint T x
  disjoint T y
  disjoint .+ x
  disjoint .+ y
  disjoint .+^ x
  disjoint .+^ y
  disjoint X x
  disjoint X y
  disjoint Y x
  disjoint Y y
  assert |- ( ph -> F e. ( S GrpHom T ) )

  proof
    wph
    cS
    cgrp
    wcel
    #
    cT
    cgrp
    wcel
    #
    wa
    cX
    cY
    cF
    wf
    #
    vx
    cv
    #
    vy
    cv
    #
    c.pl
    co
    cF
    cfv
    @3
    cF
    cfv
    @4
    cF
    cfv
    c.pd
    co
    wceq
    #
    vy
    cX
    wral
    vx
    cX
    wral
    #
    wa
    cF
    cS
    cT
    cghm
    co
    wcel
    wph
    @0
    @1
    isghmd.s
    isghmd.t
    jca
    wph
    @2
    @6
    isghmd.f
    wph
    @5
    vx
    vy
    cX
    cX
    isghmd.l
    ralrimivva
    jca
    vy
    vx
    c.pl
    c.pd
    cS
    cT
    cF
    cX
    cY
    isghmd.x
    isghmd.y
    isghmd.a
    isghmd.b
    isghm
    sylanbrc
end
