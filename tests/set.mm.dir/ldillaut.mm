include "wcel.mm"
include "wa.mm"
include "cv.mm"
include "cple.mm"
include "cfv.mm"
include "wbr.mm"
include "wceq.mm"
include "wi.mm"
include "cbs.mm"
include "wral.mm"
include "eqid.mm"
include "isldil.mm"
include "simprbda.mm"

theorem ldillaut
  let cD: class D
  let cF: class F
  let cH: class H
  let cI: class I
  let cK: class K
  let cV: class V
  let cW: class W
  let vx: setvar x
  assume ldillaut.h: |- H = ( LHyp ` K )
  assume ldillaut.i: |- I = ( LAut ` K )
  assume ldillaut.d: |- D = ( ( LDil ` K ) ` W )


  assert |- ( ( ( K e. V /\ W e. H ) /\ F e. D ) -> F e. I )

  proof
    cK
    cV
    wcel
    cW
    cH
    wcel
    wa
    cF
    cD
    wcel
    cF
    cI
    wcel
    vx
    cv
    #
    cW
    cK
    cple
    cfv
    #
    wbr
    @0
    cF
    cfv
    @0
    wceq
    wi
    vx
    cK
    cbs
    cfv
    #
    wral
    vx
    @2
    cV
    cD
    cF
    cH
    cI
    cK
    @1
    cW
    @2
    eqid
    @1
    eqid
    ldillaut.h
    ldillaut.i
    ldillaut.d
    isldil
    simprbda
end
