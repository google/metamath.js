include "cdm.mm"
include "cuni.mm"
include "cr.mm"
include "wf.mm"
include "ccnv.mm"
include "cv.mm"
include "cima.mm"
include "wcel.mm"
include "cbrsiga.mm"
include "wral.mm"
include "crrv.mm"
include "cfv.mm"
include "wa.mm"
include "isrrvv.mm"
include "mpbid.mm"
include "simpld.mm"

theorem rrvvf
  let wph: wff ph
  let cP: class P
  let cX: class X
  let vp: setvar p
  let vy: setvar y
  assume isrrvv.1: |- ( ph -> P e. Prob )
  assume rrvvf.1: |- ( ph -> X e. ( rRndVar ` P ) )


  assert |- ( ph -> X : U. dom P --> RR )

  proof
    wph
    cP
    cdm
    #
    cuni
    cr
    cX
    wf
    #
    cX
    ccnv
    vy
    cv
    cima
    @0
    wcel
    vy
    cbrsiga
    wral
    #
    wph
    cX
    cP
    crrv
    cfv
    wcel
    @1
    @2
    wa
    rrvvf.1
    wph
    vy
    cP
    cX
    isrrvv.1
    isrrvv
    mpbid
    simpld
end
