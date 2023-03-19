include "cdm.mm"
include "cuni.mm"
include "cr.mm"
include "wf.mm"
include "crn.mm"
include "wss.mm"
include "rrvvf.mm"
include "frn.mm"
include "syl.mm"

theorem rrvrnss
  let wph: wff ph
  let cP: class P
  let cX: class X
  let vp: setvar p
  let vy: setvar y
  assume isrrvv.1: |- ( ph -> P e. Prob )
  assume rrvvf.1: |- ( ph -> X e. ( rRndVar ` P ) )


  assert |- ( ph -> ran X C_ RR )

  proof
    wph
    cP
    cdm
    cuni
    #
    cr
    cX
    wf
    cX
    crn
    cr
    wss
    wph
    cP
    cX
    isrrvv.1
    rrvvf.1
    rrvvf
    @0
    cr
    cX
    frn
    syl
end
