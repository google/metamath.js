include "ghmgrp.mm"
include "wfo.mm"
include "wf.mm"
include "fof.mm"
include "syl.mm"
include "cv.mm"
include "wcel.mm"
include "co.mm"
include "cfv.mm"
include "wceq.mm"
include "3expb.mm"
include "isghmd.mm"

theorem ghmfghm
  let wph: wff ph
  let vx: setvar x
  let vy: setvar y
  let c.pl: class .+
  let c.pd: class .+^
  let cF: class F
  let cG: class G
  let cH: class H
  let cX: class X
  let cY: class Y
  let va: setvar a
  let vb: setvar b
  let vi: setvar i
  let vj: setvar j
  assume ghmabl.x: |- X = ( Base ` G )
  assume ghmabl.y: |- Y = ( Base ` H )
  assume ghmabl.p: |- .+ = ( +g ` G )
  assume ghmabl.q: |- .+^ = ( +g ` H )
  assume ghmabl.f: |- ( ( ph /\ x e. X /\ y e. X ) -> ( F ` ( x .+ y ) ) = ( ( F ` x ) .+^ ( F ` y ) ) )
  assume ghmabl.1: |- ( ph -> F : X -onto-> Y )
  assume ghmfghm.3: |- ( ph -> G e. Grp )

  disjoint .+ x
  disjoint .+ y
  disjoint x y
  disjoint .+^ x
  disjoint .+^ y
  disjoint F x
  disjoint F y
  disjoint G x
  disjoint G y
  disjoint H x
  disjoint H y
  disjoint X x
  disjoint X y
  disjoint Y x
  disjoint Y y
  disjoint ph x
  disjoint ph y
  disjoint .+^ a
  disjoint .+^ b
  disjoint a b
  disjoint a x
  disjoint a y
  disjoint b x
  disjoint b y
  disjoint F a
  disjoint F b
  disjoint H i
  disjoint H j
  disjoint i j
  disjoint i x
  disjoint i y
  disjoint j x
  disjoint j y
  disjoint X a
  disjoint X b
  disjoint Y a
  disjoint Y b
  disjoint Y i
  disjoint Y j
  disjoint a i
  disjoint a j
  disjoint b i
  disjoint b j
  disjoint a ph
  disjoint b ph
  disjoint i ph
  disjoint j ph
  assert |- ( ph -> F e. ( G GrpHom H ) )

  proof
    wph
    vx
    vy
    c.pl
    c.pd
    cG
    cH
    cF
    cX
    cY
    ghmabl.x
    ghmabl.y
    ghmabl.p
    ghmabl.q
    ghmfghm.3
    wph
    vx
    vy
    c.pl
    c.pd
    cF
    cG
    cH
    cX
    cY
    ghmabl.f
    ghmabl.x
    ghmabl.y
    ghmabl.p
    ghmabl.q
    ghmabl.1
    ghmfghm.3
    ghmgrp
    wph
    cX
    cY
    cF
    wfo
    cX
    cY
    cF
    wf
    ghmabl.1
    cX
    cY
    cF
    fof
    syl
    wph
    vx
    cv
    #
    cX
    wcel
    vy
    cv
    #
    cX
    wcel
    @0
    @1
    c.pl
    co
    cF
    cfv
    @0
    cF
    cfv
    @1
    cF
    cfv
    c.pd
    co
    wceq
    ghmabl.f
    3expb
    isghmd
end
