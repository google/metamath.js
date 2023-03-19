include "cdm.mm"
include "cr.mm"
include "wf.mm"
include "cuni.mm"
include "rrvvf.mm"
include "rrvdm.mm"
include "feq2d.mm"
include "mpbird.mm"

theorem rrvf2
  let wph: wff ph
  let cP: class P
  let cX: class X
  let vp: setvar p
  let vy: setvar y
  assume isrrvv.1: |- ( ph -> P e. Prob )
  assume rrvvf.1: |- ( ph -> X e. ( rRndVar ` P ) )


  assert |- ( ph -> X : dom X --> RR )

  proof
    wph
    cX
    cdm
    #
    cr
    cX
    wf
    cP
    cdm
    cuni
    #
    cr
    cX
    wf
    wph
    cP
    cX
    isrrvv.1
    rrvvf.1
    rrvvf
    wph
    @0
    @1
    cr
    cX
    wph
    cP
    cX
    isrrvv.1
    rrvvf.1
    rrvdm
    feq2d
    mpbird
end
