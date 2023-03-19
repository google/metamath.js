include "wcel.mm"
include "co.mm"
include "cfv.mm"
include "wceq.mm"
include "id.mm"
include "w3a.mm"
include "wi.mm"
include "cv.mm"
include "eleq1.mm"
include "3anbi2d.mm"
include "oveq1.mm"
include "fveq2d.mm"
include "fveq2.mm"
include "oveq1d.mm"
include "eqeq12d.mm"
include "imbi12d.mm"
include "3anbi3d.mm"
include "oveq2.mm"
include "oveq2d.mm"
include "vtocl2g.mm"
include "syl2anc.mm"
include "mp3and.mm"

theorem mhmlem
  let wph: wff ph
  let vx: setvar x
  let vy: setvar y
  let cA: class A
  let cB: class B
  let c.pl: class .+
  let c.pd: class .+^
  let cF: class F
  let cX: class X
  let va: setvar a
  let vd: setvar d
  let vf: setvar f
  let vi: setvar i
  let vj: setvar j
  let vk: setvar k
  let cG: class G
  let cH: class H
  let vb: setvar b
  let vc: setvar c
  let cY: class Y
  assume ghmgrp.f: |- ( ( ph /\ x e. X /\ y e. X ) -> ( F ` ( x .+ y ) ) = ( ( F ` x ) .+^ ( F ` y ) ) )
  assume mhmlem.a: |- ( ph -> A e. X )
  assume mhmlem.b: |- ( ph -> B e. X )

  disjoint A x
  disjoint A y
  disjoint x y
  disjoint B y
  disjoint F x
  disjoint F y
  disjoint x y
  disjoint .+ x
  disjoint .+ y
  disjoint X x
  disjoint X y
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
  disjoint G x
  disjoint G y
  disjoint .+ i
  disjoint .+ j
  disjoint .+ k
  disjoint H a
  disjoint H b
  disjoint H c
  disjoint H d
  disjoint H f
  disjoint H i
  disjoint H x
  disjoint H y
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
  disjoint Y x
  disjoint Y y
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
  assert |- ( ph -> ( F ` ( A .+ B ) ) = ( ( F ` A ) .+^ ( F ` B ) ) )

  proof
    wph
    wph
    cA
    cX
    wcel
    #
    cB
    cX
    wcel
    #
    cA
    cB
    c.pl
    co
    #
    cF
    cfv
    #
    cA
    cF
    cfv
    #
    cB
    cF
    cfv
    #
    c.pd
    co
    #
    wceq
    #
    wph
    id
    mhmlem.a
    mhmlem.b
    wph
    @0
    @1
    wph
    @0
    @1
    w3a
    #
    @7
    wi
    #
    mhmlem.a
    mhmlem.b
    wph
    vx
    cv
    #
    cX
    wcel
    #
    vy
    cv
    #
    cX
    wcel
    #
    w3a
    #
    @10
    @12
    c.pl
    co
    #
    cF
    cfv
    #
    @10
    cF
    cfv
    #
    @12
    cF
    cfv
    #
    c.pd
    co
    #
    wceq
    #
    wi
    wph
    @0
    @13
    w3a
    #
    cA
    @12
    c.pl
    co
    #
    cF
    cfv
    #
    @4
    @18
    c.pd
    co
    #
    wceq
    #
    wi
    @9
    vx
    vy
    cA
    cB
    cX
    cX
    @10
    cA
    wceq
    #
    @14
    @21
    @20
    @25
    @26
    @11
    @0
    wph
    @13
    @10
    cA
    cX
    eleq1
    3anbi2d
    @26
    @16
    @23
    @19
    @24
    @26
    @15
    @22
    cF
    @10
    cA
    @12
    c.pl
    oveq1
    fveq2d
    @26
    @17
    @4
    @18
    c.pd
    @10
    cA
    cF
    fveq2
    oveq1d
    eqeq12d
    imbi12d
    @12
    cB
    wceq
    #
    @21
    @8
    @25
    @7
    @27
    @13
    @1
    wph
    @0
    @12
    cB
    cX
    eleq1
    3anbi3d
    @27
    @23
    @3
    @24
    @6
    @27
    @22
    @2
    cF
    @12
    cB
    cA
    c.pl
    oveq2
    fveq2d
    @27
    @18
    @5
    @4
    c.pd
    @12
    cB
    cF
    fveq2
    oveq2d
    eqeq12d
    imbi12d
    ghmgrp.f
    vtocl2g
    syl2anc
    mp3and
end
