include "cv.mm"
include "cop.mm"
include "co.mm"
include "c2nd.mm"
include "cfv.mm"
include "cvv.mm"
include "hof2val.mm"
include "wceq.mm"
include "wa.mm"
include "simpr.mm"
include "oveq2d.mm"
include "oveq1d.mm"
include "ovexd.mm"
include "fvmptd.mm"

theorem hof2
  let wph: wff ph
  let cB: class B
  let cC: class C
  let c.x: class .x.
  let cF: class F
  let cG: class G
  let cH: class H
  let cK: class K
  let cM: class M
  let cW: class W
  let cX: class X
  let cY: class Y
  let cZ: class Z
  let vb: setvar b
  let vc: setvar c
  let vf: setvar f
  let vg: setvar g
  let vh: setvar h
  let vx: setvar x
  let vy: setvar y
  assume hofval.m: |- M = ( HomF ` C )
  assume hofval.c: |- ( ph -> C e. Cat )
  assume hof1.b: |- B = ( Base ` C )
  assume hof1.h: |- H = ( Hom ` C )
  assume hof1.x: |- ( ph -> X e. B )
  assume hof1.y: |- ( ph -> Y e. B )
  assume hof2.z: |- ( ph -> Z e. B )
  assume hof2.w: |- ( ph -> W e. B )
  assume hof2.o: |- .x. = ( comp ` C )
  assume hof2.f: |- ( ph -> F e. ( Z H X ) )
  assume hof2.g: |- ( ph -> G e. ( Y H W ) )
  assume hof2.k: |- ( ph -> K e. ( X H Y ) )


  assert |- ( ph -> ( ( F ( <. X , Y >. ( 2nd ` M ) <. Z , W >. ) G ) ` K ) = ( ( G ( <. X , Y >. .x. W ) K ) ( <. Z , X >. .x. W ) F ) )

  proof
    wph
    vh
    cK
    cG
    vh
    cv
    #
    cX
    cY
    cop
    #
    cW
    c.x
    co
    #
    co
    #
    cF
    cZ
    cX
    cop
    cW
    c.x
    co
    #
    co
    cG
    cK
    @2
    co
    #
    cF
    @4
    co
    cX
    cY
    cH
    co
    cF
    cG
    @1
    cZ
    cW
    cop
    cM
    c2nd
    cfv
    co
    co
    cvv
    wph
    cB
    cC
    c.x
    vh
    cF
    cG
    cH
    cM
    cW
    cX
    cY
    cZ
    hofval.m
    hofval.c
    hof1.b
    hof1.h
    hof1.x
    hof1.y
    hof2.z
    hof2.w
    hof2.o
    hof2.f
    hof2.g
    hof2val
    wph
    @0
    cK
    wceq
    #
    wa
    #
    @3
    @5
    cF
    @4
    @7
    @0
    cK
    cG
    @2
    wph
    @6
    simpr
    oveq2d
    oveq1d
    hof2.k
    wph
    @5
    cF
    @4
    ovexd
    fvmptd
end
