include "ccphlo.mm"
include "wcel.mm"
include "ccbn.mm"
include "w3a.mm"
include "chlo.mm"
include "simp3.mm"
include "sspph.mm"
include "3adant3.mm"
include "ishlo.mm"
include "sylanbrc.mm"

theorem ssphl
  let cU: class U
  let cH: class H
  let cW: class W
  assume ssphl.h: |- H = ( SubSp ` U )


  assert |- ( ( U e. CPreHilOLD /\ W e. H /\ W e. CBan ) -> W e. CHilOLD )

  proof
    cU
    ccphlo
    wcel
    #
    cW
    cH
    wcel
    #
    cW
    ccbn
    wcel
    #
    w3a
    @2
    cW
    ccphlo
    wcel
    #
    cW
    chlo
    wcel
    @0
    @1
    @2
    simp3
    @0
    @1
    @3
    @2
    cU
    cH
    cW
    ssphl.h
    sspph
    3adant3
    cW
    ishlo
    sylanbrc
end
