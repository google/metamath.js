include "ccarsg.mm"
include "cfv.mm"
include "cv.mm"
include "cin.mm"
include "cdif.mm"
include "cxad.mm"
include "co.mm"
include "wceq.mm"
include "cpw.mm"
include "wral.mm"
include "crab.mm"
include "carsgval.mm"
include "ssrab2.mm"
include "syl6eqss.mm"

theorem carsgcl
  let wph: wff ph
  let cM: class M
  let cO: class O
  let cV: class V
  let va: setvar a
  let ve: setvar e
  let vm: setvar m
  assume carsgval.1: |- ( ph -> O e. V )
  assume carsgval.2: |- ( ph -> M : ~P O --> ( 0 [,] +oo ) )


  assert |- ( ph -> ( toCaraSiga ` M ) C_ ~P O )

  proof
    wph
    cM
    ccarsg
    cfv
    ve
    cv
    #
    va
    cv
    #
    cin
    cM
    cfv
    @0
    @1
    cdif
    cM
    cfv
    cxad
    co
    @0
    cM
    cfv
    wceq
    ve
    cO
    cpw
    #
    wral
    #
    va
    @2
    crab
    @2
    wph
    ve
    cM
    cO
    cV
    va
    carsgval.1
    carsgval.2
    carsgval
    @3
    va
    @2
    ssrab2
    syl6eqss
end
