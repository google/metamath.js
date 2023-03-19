include "cmnd.mm"
include "wcel.mm"
include "cv.mm"
include "co.mm"
include "c0g.mm"
include "cfv.mm"
include "wceq.mm"
include "wrex.mm"
include "wral.mm"
include "cgrp.mm"
include "grpmnd.mm"
include "syl.mm"
include "mhmmnd.mm"
include "wa.mm"
include "cminusg.mm"
include "wf.mm"
include "wfo.mm"
include "fof.mm"
include "ad3antrrr.mm"
include "simplr.mm"
include "eqid.mm"
include "grpinvcl.mm"
include "syl2anc.mm"
include "ffvelrnd.mm"
include "3adant1r.mm"
include "sylan.mm"
include "simpr.mm"
include "mhmlem.mm"
include "adantlr.mm"
include "adantr.mm"
include "grplinv.mm"
include "fveq2d.mm"
include "mhmid.mm"
include "eqtrd.mm"
include "oveq2d.mm"
include "3eqtr3rd.mm"
include "oveq1.mm"
include "eqeq1d.mm"
include "rspcev.mm"
include "foelrni.mm"
include "r19.29a.mm"
include "ralrimiva.mm"
include "isgrp.mm"
include "sylanbrc.mm"

theorem ghmgrp
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
  assume ghmgrp.3: |- ( ph -> G e. Grp )

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
  assert |- ( ph -> H e. Grp )

  proof
    wph
    cH
    cmnd
    wcel
    vf
    cv
    #
    va
    cv
    #
    c.pd
    co
    #
    cH
    c0g
    cfv
    #
    wceq
    #
    vf
    cY
    wrex
    #
    va
    cY
    wral
    cH
    cgrp
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
    ghmgrp.f
    ghmgrp.x
    ghmgrp.y
    ghmgrp.p
    ghmgrp.q
    ghmgrp.1
    wph
    cG
    cgrp
    wcel
    #
    cG
    cmnd
    wcel
    ghmgrp.3
    cG
    grpmnd
    syl
    #
    mhmmnd
    wph
    @5
    va
    cY
    wph
    @1
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
    @1
    wceq
    #
    @5
    vi
    cX
    @9
    @10
    cX
    wcel
    #
    wa
    #
    @12
    wa
    #
    @10
    cG
    cminusg
    cfv
    #
    cfv
    #
    cF
    cfv
    #
    cY
    wcel
    @18
    @1
    c.pd
    co
    #
    @3
    wceq
    #
    @5
    @15
    cX
    cY
    @17
    cF
    wph
    cX
    cY
    cF
    wf
    #
    @8
    @13
    @12
    wph
    cX
    cY
    cF
    wfo
    #
    @21
    ghmgrp.1
    cX
    cY
    cF
    fof
    syl
    ad3antrrr
    @15
    @6
    @13
    @17
    cX
    wcel
    #
    wph
    @6
    @8
    @13
    @12
    ghmgrp.3
    ad3antrrr
    #
    @9
    @13
    @12
    simplr
    #
    cX
    cG
    @16
    @10
    ghmgrp.x
    @16
    eqid
    #
    grpinvcl
    #
    syl2anc
    ffvelrnd
    @15
    @17
    @10
    c.pl
    co
    #
    cF
    cfv
    #
    @18
    @11
    c.pd
    co
    #
    @3
    @19
    @14
    @29
    @30
    wceq
    #
    @12
    wph
    @13
    @31
    @8
    wph
    @13
    wa
    vx
    vy
    @17
    @10
    c.pl
    c.pd
    cF
    cX
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
    @32
    @33
    c.pl
    co
    cF
    cfv
    @32
    cF
    cfv
    @33
    cF
    cfv
    c.pd
    co
    wceq
    @13
    ghmgrp.f
    3adant1r
    wph
    @6
    @13
    @23
    ghmgrp.3
    @27
    sylan
    wph
    @13
    simpr
    mhmlem
    adantlr
    adantr
    @15
    @29
    cG
    c0g
    cfv
    #
    cF
    cfv
    #
    @3
    @15
    @6
    @13
    @29
    @35
    wceq
    @24
    @25
    @6
    @13
    wa
    @28
    @34
    cF
    cX
    c.pl
    cG
    @16
    @10
    @34
    ghmgrp.x
    ghmgrp.p
    @34
    eqid
    #
    @26
    grplinv
    fveq2d
    syl2anc
    wph
    @35
    @3
    wceq
    @8
    @13
    @12
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
    @34
    ghmgrp.f
    ghmgrp.x
    ghmgrp.y
    ghmgrp.p
    ghmgrp.q
    ghmgrp.1
    @7
    @36
    mhmid
    ad3antrrr
    eqtrd
    @15
    @11
    @1
    @18
    c.pd
    @14
    @12
    simpr
    oveq2d
    3eqtr3rd
    @4
    @20
    vf
    @18
    cY
    @0
    @18
    wceq
    @2
    @19
    @3
    @0
    @18
    @1
    c.pd
    oveq1
    eqeq1d
    rspcev
    syl2anc
    wph
    @22
    @8
    @12
    vi
    cX
    wrex
    ghmgrp.1
    vi
    cX
    cY
    cF
    @1
    foelrni
    sylan
    r19.29a
    ralrimiva
    cY
    c.pd
    vf
    cH
    @3
    va
    ghmgrp.y
    ghmgrp.q
    @3
    eqid
    isgrp
    sylanbrc
end
