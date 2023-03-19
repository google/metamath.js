include "cdm.mm"
include "cuni.mm"
include "cr.mm"
include "wf.mm"
include "wceq.mm"
include "rrvvf.mm"
include "fdm.mm"
include "syl.mm"

theorem rrvdm
  let wph: wff ph
  let cP: class P
  let cX: class X
  let vp: setvar p
  let vy: setvar y
  assume isrrvv.1: |- ( ph -> P e. Prob )
  assume rrvvf.1: |- ( ph -> X e. ( rRndVar ` P ) )


  assert |- ( ph -> dom X = U. dom P )

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
    cdm
    @0
    wceq
    wph
    cP
    cX
    isrrvv.1
    rrvvf.1
    rrvvf
    @0
    cr
    cX
    fdm
    syl
end
