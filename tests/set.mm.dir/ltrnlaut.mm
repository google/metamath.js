include "wcel.mm"
include "wa.mm"
include "cldil.mm"
include "cfv.mm"
include "eqid.mm"
include "ltrnldil.mm"
include "ldillaut.mm"
include "syldan.mm"

theorem ltrnlaut
  let cT: class T
  let cF: class F
  let cH: class H
  let cI: class I
  let cK: class K
  let cV: class V
  let cW: class W
  assume ltrnlaut.h: |- H = ( LHyp ` K )
  assume ltrnlaut.i: |- I = ( LAut ` K )
  assume ltrnlaut.t: |- T = ( ( LTrn ` K ) ` W )


  assert |- ( ( ( K e. V /\ W e. H ) /\ F e. T ) -> F e. I )

  proof
    cK
    cV
    wcel
    cW
    cH
    wcel
    wa
    cF
    cT
    wcel
    cF
    cW
    cK
    cldil
    cfv
    cfv
    #
    wcel
    cF
    cI
    wcel
    @0
    cT
    cF
    cH
    cK
    cV
    cW
    ltrnlaut.h
    @0
    eqid
    #
    ltrnlaut.t
    ltrnldil
    @0
    cF
    cH
    cI
    cK
    cV
    cW
    ltrnlaut.h
    ltrnlaut.i
    @1
    ldillaut
    syldan
end
