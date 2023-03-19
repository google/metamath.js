include "ccic.mm"
include "cfv.mm"
include "wbr.mm"
include "co.mm"
include "c0.mm"
include "wne.mm"
include "cv.mm"
include "wcel.mm"
include "wex.mm"
include "brcic.mm"
include "n0.mm"
include "syl6bb.mm"

theorem cic
  let wph: wff ph
  let cB: class B
  let cC: class C
  let vf: setvar f
  let cI: class I
  let cX: class X
  let cY: class Y
  assume cic.i: |- I = ( Iso ` C )
  assume cic.b: |- B = ( Base ` C )
  assume cic.c: |- ( ph -> C e. Cat )
  assume cic.x: |- ( ph -> X e. B )
  assume cic.y: |- ( ph -> Y e. B )

  disjoint I f
  disjoint X f
  disjoint Y f
  assert |- ( ph -> ( X ( ~=c ` C ) Y <-> E. f f e. ( X I Y ) ) )

  proof
    wph
    cX
    cY
    cC
    ccic
    cfv
    wbr
    cX
    cY
    cI
    co
    #
    c0
    wne
    vf
    cv
    @0
    wcel
    vf
    wex
    wph
    cB
    cC
    cI
    cX
    cY
    cic.i
    cic.b
    cic.c
    cic.x
    cic.y
    brcic
    vf
    @0
    n0
    syl6bb
end
