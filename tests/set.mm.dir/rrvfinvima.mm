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
include "simprd.mm"

theorem rrvfinvima
  let wph: wff ph
  let vy: setvar y
  let cP: class P
  let cX: class X
  let vp: setvar p
  assume isrrvv.1: |- ( ph -> P e. Prob )
  assume rrvvf.1: |- ( ph -> X e. ( rRndVar ` P ) )

  disjoint P y
  disjoint X y
  disjoint p y
  disjoint P p
  assert |- ( ph -> A. y e. BrSiga ( `' X " y ) e. dom P )

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
    simprd
end
