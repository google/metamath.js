include "cgrp.mm"
include "wcel.mm"
include "ccmn.mm"
include "cabl.mm"
include "ablgrp.mm"
include "syl.mm"
include "ghmgrp.mm"
include "ablcmn.mm"
include "ghmcmn.mm"
include "isabl.mm"
include "sylanbrc.mm"

theorem ghmabl
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
  assume ghmabl.3: |- ( ph -> G e. Abel )

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
  assert |- ( ph -> H e. Abel )

  proof
    wph
    cH
    cgrp
    wcel
    cH
    ccmn
    wcel
    cH
    cabl
    wcel
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
    wph
    cG
    cabl
    wcel
    #
    cG
    cgrp
    wcel
    ghmabl.3
    cG
    ablgrp
    syl
    ghmgrp
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
    ghmabl.x
    ghmabl.y
    ghmabl.p
    ghmabl.q
    ghmabl.f
    ghmabl.1
    wph
    @0
    cG
    ccmn
    wcel
    ghmabl.3
    cG
    ablcmn
    syl
    ghmcmn
    cH
    isabl
    sylanbrc
end
