include "co.mm"
include "cv.mm"
include "cop.mm"
include "cmpt.mm"
include "c2nd.mm"
include "cfv.mm"
include "cvv.mm"
include "hof2fval.mm"
include "wceq.mm"
include "wa.mm"
include "wcel.mm"
include "simplrr.mm"
include "oveq1d.mm"
include "simplrl.mm"
include "oveq12d.mm"
include "mpteq2dva.mm"
include "ovex.mm"
include "mptex.mm"
include "a1i.mm"
include "ovmpt2d.mm"

theorem hof2val
  let wph: wff ph
  let cB: class B
  let cC: class C
  let c.x: class .x.
  let vh: setvar h
  let cF: class F
  let cG: class G
  let cH: class H
  let cM: class M
  let cW: class W
  let cX: class X
  let cY: class Y
  let cZ: class Z
  let vb: setvar b
  let vc: setvar c
  let vf: setvar f
  let vg: setvar g
  let vx: setvar x
  let vy: setvar y
  let cK: class K
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

  disjoint B h
  disjoint F h
  disjoint G h
  disjoint h ph
  disjoint C h
  disjoint H h
  disjoint W h
  disjoint .x. h
  disjoint X h
  disjoint Y h
  disjoint Z h
  disjoint b c
  disjoint b f
  disjoint b g
  disjoint b h
  disjoint b x
  disjoint b y
  disjoint B b
  disjoint c f
  disjoint c g
  disjoint c h
  disjoint c x
  disjoint c y
  disjoint B c
  disjoint f g
  disjoint f h
  disjoint f x
  disjoint f y
  disjoint B f
  disjoint g h
  disjoint g x
  disjoint g y
  disjoint B g
  disjoint h x
  disjoint h y
  disjoint x y
  disjoint B x
  disjoint B y
  disjoint F f
  disjoint F g
  disjoint G f
  disjoint G g
  disjoint b ph
  disjoint c ph
  disjoint f ph
  disjoint g ph
  disjoint ph x
  disjoint ph y
  disjoint C b
  disjoint C c
  disjoint C f
  disjoint C g
  disjoint C x
  disjoint C y
  disjoint H b
  disjoint H c
  disjoint H f
  disjoint H g
  disjoint H x
  disjoint H y
  disjoint K h
  disjoint W f
  disjoint W g
  disjoint W x
  disjoint W y
  disjoint .x. b
  disjoint .x. c
  disjoint .x. f
  disjoint .x. g
  disjoint .x. x
  disjoint .x. y
  disjoint X f
  disjoint X g
  disjoint X x
  disjoint X y
  disjoint Y f
  disjoint Y g
  disjoint Y x
  disjoint Y y
  disjoint Z f
  disjoint Z g
  disjoint Z x
  disjoint Z y
  assert |- ( ph -> ( F ( <. X , Y >. ( 2nd ` M ) <. Z , W >. ) G ) = ( h e. ( X H Y ) |-> ( ( G ( <. X , Y >. .x. W ) h ) ( <. Z , X >. .x. W ) F ) ) )

  proof
    wph
    vf
    vg
    cF
    cG
    cZ
    cX
    cH
    co
    cY
    cW
    cH
    co
    vh
    cX
    cY
    cH
    co
    #
    vg
    cv
    #
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
    vf
    cv
    #
    cZ
    cX
    cop
    cW
    c.x
    co
    #
    co
    #
    cmpt
    vh
    @0
    cG
    @2
    @4
    co
    #
    cF
    @7
    co
    #
    cmpt
    #
    @3
    cZ
    cW
    cop
    cM
    c2nd
    cfv
    co
    cvv
    wph
    cB
    cC
    c.x
    vf
    vg
    vh
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
    hof2fval
    wph
    @6
    cF
    wceq
    #
    @1
    cG
    wceq
    #
    wa
    wa
    #
    vh
    @0
    @8
    @10
    @14
    @2
    @0
    wcel
    #
    wa
    #
    @5
    @9
    @6
    cF
    @7
    @16
    @1
    cG
    @2
    @4
    wph
    @12
    @13
    @15
    simplrr
    oveq1d
    wph
    @12
    @13
    @15
    simplrl
    oveq12d
    mpteq2dva
    hof2.f
    hof2.g
    @11
    cvv
    wcel
    wph
    vh
    @0
    @10
    cX
    cY
    cH
    ovex
    mptex
    a1i
    ovmpt2d
end
