include "co.mm"
include "c2nd.mm"
include "cfv.mm"
include "cop.mm"
include "cotp.mm"
include "coaval.mm"
include "fveq2d.mm"
include "cvv.mm"
include "wcel.mm"
include "wceq.mm"
include "ovex.mm"
include "ot3rdg.mm"
include "ax-mp.mm"
include "syl6eq.mm"

theorem coa2
  let wph: wff ph
  let cC: class C
  let c.xb: class .xb
  let c.x: class .x.
  let cF: class F
  let cG: class G
  let cH: class H
  let cX: class X
  let cY: class Y
  let cZ: class Z
  let vf: setvar f
  let vg: setvar g
  let vh: setvar h
  assume homdmcoa.o: |- .x. = ( compA ` C )
  assume homdmcoa.h: |- H = ( HomA ` C )
  assume homdmcoa.f: |- ( ph -> F e. ( X H Y ) )
  assume homdmcoa.g: |- ( ph -> G e. ( Y H Z ) )
  assume coaval.x: |- .xb = ( comp ` C )


  assert |- ( ph -> ( 2nd ` ( G .x. F ) ) = ( ( 2nd ` G ) ( <. X , Y >. .xb Z ) ( 2nd ` F ) ) )

  proof
    wph
    cG
    cF
    c.x
    co
    #
    c2nd
    cfv
    cX
    cZ
    cG
    c2nd
    cfv
    #
    cF
    c2nd
    cfv
    #
    cX
    cY
    cop
    cZ
    c.xb
    co
    #
    co
    #
    cotp
    #
    c2nd
    cfv
    #
    @4
    wph
    @0
    @5
    c2nd
    wph
    cC
    c.xb
    c.x
    cF
    cG
    cH
    cX
    cY
    cZ
    homdmcoa.o
    homdmcoa.h
    homdmcoa.f
    homdmcoa.g
    coaval.x
    coaval
    fveq2d
    @4
    cvv
    wcel
    @6
    @4
    wceq
    @1
    @2
    @3
    ovex
    cX
    cZ
    @4
    cvv
    ot3rdg
    ax-mp
    syl6eq
end
