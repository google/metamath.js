include "crngo.mm"
include "wcel.mm"
include "crn.mm"
include "cdm.mm"
include "cgr.mm"
include "wceq.mm"
include "rngogrpo.mm"
include "grporndm.mm"
include "syl.mm"
include "rngodm1dm2.mm"
include "eqtrd.mm"

theorem rngorn1
  let cR: class R
  let cG: class G
  let cH: class H
  assume rnplrnml0.1: |- H = ( 2nd ` R )
  assume rnplrnml0.2: |- G = ( 1st ` R )


  assert |- ( R e. RingOps -> ran G = dom dom H )

  proof
    cR
    crngo
    wcel
    #
    cG
    crn
    #
    cG
    cdm
    cdm
    #
    cH
    cdm
    cdm
    @0
    cG
    cgr
    wcel
    @1
    @2
    wceq
    cR
    cG
    rnplrnml0.2
    rngogrpo
    cG
    grporndm
    syl
    cR
    cG
    cH
    rnplrnml0.1
    rnplrnml0.2
    rngodm1dm2
    eqtrd
end
