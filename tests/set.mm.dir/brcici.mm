include "ccic.mm"
include "cfv.mm"
include "wbr.mm"
include "cv.mm"
include "co.mm"
include "wcel.mm"
include "wex.mm"
include "eleq1.mm"
include "spcegv.mm"
include "sylc.mm"
include "cic.mm"
include "mpbird.mm"

theorem brcici
  let wph: wff ph
  let cB: class B
  let cC: class C
  let cF: class F
  let cI: class I
  let cX: class X
  let cY: class Y
  let vf: setvar f
  assume cic.i: |- I = ( Iso ` C )
  assume cic.b: |- B = ( Base ` C )
  assume cic.c: |- ( ph -> C e. Cat )
  assume cic.x: |- ( ph -> X e. B )
  assume cic.y: |- ( ph -> Y e. B )
  assume cic.f: |- ( ph -> F e. ( X I Y ) )


  assert |- ( ph -> X ( ~=c ` C ) Y )

  proof
    wph
    cX
    cY
    cC
    ccic
    cfv
    wbr
    vf
    cv
    #
    cX
    cY
    cI
    co
    #
    wcel
    #
    vf
    wex
    #
    wph
    cF
    @1
    wcel
    #
    @4
    @3
    cic.f
    cic.f
    @2
    @4
    vf
    cF
    @1
    @0
    cF
    @1
    eleq1
    spcegv
    sylc
    wph
    cB
    cC
    vf
    cI
    cX
    cY
    cic.i
    cic.b
    cic.c
    cic.x
    cic.y
    cic
    mpbird
end
