include "cmnd.mm"
include "wcel.mm"
include "wa.mm"
include "wf.mm"
include "cv.mm"
include "co.mm"
include "cfv.mm"
include "wceq.mm"
include "wral.mm"
include "c0g.mm"
include "w3a.mm"
include "cmhm.mm"
include "mhmmnd.mm"
include "wfo.mm"
include "fof.mm"
include "syl.mm"
include "3expb.mm"
include "ralrimivva.mm"
include "eqid.mm"
include "mhmid.mm"
include "3jca.mm"
include "jca31.mm"
include "ismhm.mm"
include "sylibr.mm"

theorem mhmfmhm
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
  let vd: setvar d
  let vf: setvar f
  let vi: setvar i
  let vj: setvar j
  let vk: setvar k
  let vb: setvar b
  let vc: setvar c
  assume ghmgrp.f: |- ( ( ph /\ x e. X /\ y e. X ) -> ( F ` ( x .+ y ) ) = ( ( F ` x ) .+^ ( F ` y ) ) )
  assume ghmgrp.x: |- X = ( Base ` G )
  assume ghmgrp.y: |- Y = ( Base ` H )
  assume ghmgrp.p: |- .+ = ( +g ` G )
  assume ghmgrp.q: |- .+^ = ( +g ` H )
  assume ghmgrp.1: |- ( ph -> F : X -onto-> Y )
  assume mhmmnd.3: |- ( ph -> G e. Mnd )

  disjoint F x
  disjoint F y
  disjoint x y
  disjoint G x
  disjoint G y
  disjoint .+ x
  disjoint .+ y
  disjoint H x
  disjoint H y
  disjoint X x
  disjoint X y
  disjoint Y x
  disjoint Y y
  disjoint .+^ x
  disjoint .+^ y
  disjoint ph x
  disjoint ph y
  disjoint F a
  disjoint F d
  disjoint F f
  disjoint F i
  disjoint F j
  disjoint F k
  disjoint a d
  disjoint a f
  disjoint a i
  disjoint a j
  disjoint a k
  disjoint a x
  disjoint a y
  disjoint d f
  disjoint d i
  disjoint d j
  disjoint d k
  disjoint d x
  disjoint d y
  disjoint f i
  disjoint f j
  disjoint f k
  disjoint f x
  disjoint f y
  disjoint i j
  disjoint i k
  disjoint i x
  disjoint i y
  disjoint j k
  disjoint j x
  disjoint j y
  disjoint k x
  disjoint k y
  disjoint G a
  disjoint G d
  disjoint G f
  disjoint G i
  disjoint G j
  disjoint G k
  disjoint .+ i
  disjoint .+ j
  disjoint .+ k
  disjoint H a
  disjoint H b
  disjoint H c
  disjoint H d
  disjoint H f
  disjoint H i
  disjoint a b
  disjoint a c
  disjoint b c
  disjoint b d
  disjoint b f
  disjoint b i
  disjoint b x
  disjoint b y
  disjoint c d
  disjoint c f
  disjoint c i
  disjoint c x
  disjoint c y
  disjoint X i
  disjoint X j
  disjoint X k
  disjoint Y a
  disjoint Y b
  disjoint Y c
  disjoint Y d
  disjoint Y f
  disjoint Y i
  disjoint Y j
  disjoint Y k
  disjoint b j
  disjoint b k
  disjoint c j
  disjoint c k
  disjoint .+^ a
  disjoint .+^ b
  disjoint .+^ c
  disjoint .+^ d
  disjoint .+^ f
  disjoint .+^ i
  disjoint .+^ j
  disjoint .+^ k
  disjoint a ph
  disjoint b ph
  disjoint c ph
  disjoint i ph
  disjoint j ph
  disjoint k ph
  assert |- ( ph -> F e. ( G MndHom H ) )

  proof
    wph
    cG
    cmnd
    wcel
    #
    cH
    cmnd
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
    cG
    c0g
    cfv
    #
    cF
    cfv
    cH
    c0g
    cfv
    #
    wceq
    #
    w3a
    #
    wa
    cF
    cG
    cH
    cmhm
    co
    wcel
    wph
    @0
    @1
    @10
    mhmmnd.3
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
    ghmgrp.f
    ghmgrp.x
    ghmgrp.y
    ghmgrp.p
    ghmgrp.q
    ghmgrp.1
    mhmmnd.3
    mhmmnd
    wph
    @2
    @6
    @9
    wph
    cX
    cY
    cF
    wfo
    @2
    ghmgrp.1
    cX
    cY
    cF
    fof
    syl
    wph
    @5
    vx
    vy
    cX
    cX
    wph
    @3
    cX
    wcel
    @4
    cX
    wcel
    @5
    ghmgrp.f
    3expb
    ralrimivva
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
    @7
    ghmgrp.f
    ghmgrp.x
    ghmgrp.y
    ghmgrp.p
    ghmgrp.q
    ghmgrp.1
    mhmmnd.3
    @7
    eqid
    #
    mhmid
    3jca
    jca31
    vx
    vy
    cX
    cY
    c.pl
    c.pd
    cG
    cH
    cF
    @8
    @7
    ghmgrp.x
    ghmgrp.y
    ghmgrp.p
    ghmgrp.q
    @11
    @8
    eqid
    ismhm
    sylibr
end
