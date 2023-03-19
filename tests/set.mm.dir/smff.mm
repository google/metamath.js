include "cuni.mm"
include "wss.mm"
include "cr.mm"
include "wf.mm"
include "cv.mm"
include "cfv.mm"
include "clt.mm"
include "wbr.mm"
include "crab.mm"
include "crest.mm"
include "co.mm"
include "wcel.mm"
include "wral.mm"
include "csmblfn.mm"
include "w3a.mm"
include "issmf.mm"
include "mpbid.mm"
include "simp2d.mm"

theorem smff
  let wph: wff ph
  let cD: class D
  let cS: class S
  let cF: class F
  let va: setvar a
  let vx: setvar x
  let vk: setvar k
  assume smff.s: |- ( ph -> S e. SAlg )
  assume smff.f: |- ( ph -> F e. ( SMblFn ` S ) )
  assume smff.d: |- D = dom F


  assert |- ( ph -> F : D --> RR )

  proof
    wph
    cD
    cS
    cuni
    wss
    #
    cD
    cr
    cF
    wf
    #
    vx
    cv
    cF
    cfv
    va
    cv
    clt
    wbr
    vx
    cD
    crab
    cS
    cD
    crest
    co
    wcel
    va
    cr
    wral
    #
    wph
    cF
    cS
    csmblfn
    cfv
    wcel
    @0
    @1
    @2
    w3a
    smff.f
    wph
    vx
    cD
    cS
    cF
    va
    smff.s
    smff.d
    issmf
    mpbid
    simp2d
end
