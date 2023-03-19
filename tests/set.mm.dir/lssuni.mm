include "cuni.mm"
include "cv.mm"
include "wss.mm"
include "crab.mm"
include "wceq.mm"
include "rabid2.mm"
include "lssss.mm"
include "mprgbir.mm"
include "unieqi.mm"
include "clmod.mm"
include "wcel.mm"
include "lss1.mm"
include "unimax.mm"
include "3syl.mm"
include "syl5eq.mm"

theorem lssuni
  let wph: wff ph
  let cS: class S
  let cV: class V
  let cW: class W
  let va: setvar a
  let vb: setvar b
  let vx: setvar x
  let cU: class U
  assume lssss.v: |- V = ( Base ` W )
  assume lssss.s: |- S = ( LSubSp ` W )
  assume lssuni.w: |- ( ph -> W e. LMod )


  assert |- ( ph -> U. S = V )

  proof
    wph
    cS
    cuni
    vx
    cv
    #
    cV
    wss
    #
    vx
    cS
    crab
    #
    cuni
    #
    cV
    cS
    @2
    cS
    @2
    wceq
    @1
    vx
    cS
    @1
    vx
    cS
    rabid2
    cS
    @0
    cV
    cW
    lssss.v
    lssss.s
    lssss
    mprgbir
    unieqi
    wph
    cW
    clmod
    wcel
    cV
    cS
    wcel
    @3
    cV
    wceq
    lssuni.w
    cS
    cV
    cW
    lssss.v
    lssss.s
    lss1
    vx
    cV
    cS
    unimax
    3syl
    syl5eq
end
