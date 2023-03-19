include "cfv.mm"
include "c0g.mm"
include "eqid.mm"
include "wfo.mm"
include "wf.mm"
include "fof.mm"
include "syl.mm"
include "cmnd.mm"
include "wcel.mm"
include "mndidcl.mm"
include "ffvelrnd.mm"
include "cv.mm"
include "wa.mm"
include "wceq.mm"
include "co.mm"
include "simplll.mm"
include "syl3an1.mm"
include "ad3antrrr.mm"
include "simplr.mm"
include "mhmlem.mm"
include "mndlid.mm"
include "syl2anc.mm"
include "fveq2d.mm"
include "eqtr3d.mm"
include "simpr.mm"
include "oveq2d.mm"
include "3eqtr3d.mm"
include "wrex.mm"
include "foelrni.mm"
include "sylan.mm"
include "r19.29a.mm"
include "mndrid.mm"
include "oveq1d.mm"
include "ismgmid2.mm"

theorem mhmid
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
  let c.0: class .0.
  let va: setvar a
  let vi: setvar i
  let vd: setvar d
  let vf: setvar f
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
  assume mhmid.0: |- .0. = ( 0g ` G )

  disjoint .0. x
  disjoint .0. y
  disjoint x y
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
  disjoint .0. a
  disjoint .0. i
  disjoint a i
  disjoint a x
  disjoint a y
  disjoint i x
  disjoint i y
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
  assert |- ( ph -> ( F ` .0. ) = ( 0g ` H ) )

  proof
    wph
    va
    cY
    c.pd
    c.0
    cF
    cfv
    #
    cH
    cH
    c0g
    cfv
    #
    ghmgrp.y
    @1
    eqid
    ghmgrp.q
    wph
    cX
    cY
    c.0
    cF
    wph
    cX
    cY
    cF
    wfo
    #
    cX
    cY
    cF
    wf
    ghmgrp.1
    cX
    cY
    cF
    fof
    syl
    wph
    cG
    cmnd
    wcel
    #
    c.0
    cX
    wcel
    #
    mhmmnd.3
    cX
    cG
    c.0
    ghmgrp.x
    mhmid.0
    mndidcl
    #
    syl
    ffvelrnd
    wph
    va
    cv
    #
    cY
    wcel
    #
    wa
    #
    vi
    cv
    #
    cF
    cfv
    #
    @6
    wceq
    #
    @0
    @6
    c.pd
    co
    #
    @6
    wceq
    vi
    cX
    @8
    @9
    cX
    wcel
    #
    wa
    #
    @11
    wa
    #
    @0
    @10
    c.pd
    co
    #
    @10
    @12
    @6
    @15
    c.0
    @9
    c.pl
    co
    #
    cF
    cfv
    @16
    @10
    @15
    vx
    vy
    c.0
    @9
    c.pl
    c.pd
    cF
    cX
    @15
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
    @18
    @19
    c.pl
    co
    cF
    cfv
    @18
    cF
    cfv
    @19
    cF
    cfv
    c.pd
    co
    wceq
    wph
    @7
    @13
    @11
    simplll
    ghmgrp.f
    syl3an1
    #
    @15
    @3
    @4
    wph
    @3
    @7
    @13
    @11
    mhmmnd.3
    ad3antrrr
    #
    @5
    syl
    #
    @8
    @13
    @11
    simplr
    #
    mhmlem
    @15
    @17
    @9
    cF
    @15
    @3
    @13
    @17
    @9
    wceq
    @21
    @23
    cX
    c.pl
    cG
    @9
    c.0
    ghmgrp.x
    ghmgrp.p
    mhmid.0
    mndlid
    syl2anc
    fveq2d
    eqtr3d
    @15
    @10
    @6
    @0
    c.pd
    @14
    @11
    simpr
    #
    oveq2d
    @24
    3eqtr3d
    wph
    @2
    @7
    @11
    vi
    cX
    wrex
    ghmgrp.1
    vi
    cX
    cY
    cF
    @6
    foelrni
    sylan
    #
    r19.29a
    @8
    @11
    @6
    @0
    c.pd
    co
    #
    @6
    wceq
    vi
    cX
    @15
    @10
    @0
    c.pd
    co
    #
    @10
    @26
    @6
    @15
    @9
    c.0
    c.pl
    co
    #
    cF
    cfv
    @27
    @10
    @15
    vx
    vy
    @9
    c.0
    c.pl
    c.pd
    cF
    cX
    @20
    @23
    @22
    mhmlem
    @15
    @28
    @9
    cF
    @15
    @3
    @13
    @28
    @9
    wceq
    @21
    @23
    cX
    c.pl
    cG
    @9
    c.0
    ghmgrp.x
    ghmgrp.p
    mhmid.0
    mndrid
    syl2anc
    fveq2d
    eqtr3d
    @15
    @10
    @6
    @0
    c.pd
    @24
    oveq1d
    @24
    3eqtr3d
    @25
    r19.29a
    ismgmid2
end
