include "chlt.mm"
include "wcel.mm"
include "wa.mm"
include "w3a.mm"
include "ccom.mm"
include "ltrncom.mm"
include "coeq1d.mm"
include "coass.mm"
include "3eqtr3g.mm"
include "coeq2d.mm"
include "3eqtr4g.mm"

theorem ltrnco4
  let cD: class D
  let cT: class T
  let cE: class E
  let cF: class F
  let cG: class G
  let cH: class H
  let cK: class K
  let cW: class W
  assume ltrncom.h: |- H = ( LHyp ` K )
  assume ltrncom.t: |- T = ( ( LTrn ` K ) ` W )


  assert |- ( ( ( K e. HL /\ W e. H ) /\ E e. T /\ F e. T ) -> ( ( D o. E ) o. ( F o. G ) ) = ( ( D o. F ) o. ( E o. G ) ) )

  proof
    cK
    chlt
    wcel
    cW
    cH
    wcel
    wa
    cE
    cT
    wcel
    cF
    cT
    wcel
    w3a
    #
    cD
    cE
    cF
    cG
    ccom
    #
    ccom
    #
    ccom
    cD
    cF
    cE
    cG
    ccom
    #
    ccom
    #
    ccom
    cD
    cE
    ccom
    @1
    ccom
    cD
    cF
    ccom
    @3
    ccom
    @0
    @2
    @4
    cD
    @0
    cE
    cF
    ccom
    #
    cG
    ccom
    cF
    cE
    ccom
    #
    cG
    ccom
    @2
    @4
    @0
    @5
    @6
    cG
    cT
    cE
    cF
    cH
    cK
    cW
    ltrncom.h
    ltrncom.t
    ltrncom
    coeq1d
    cE
    cF
    cG
    coass
    cF
    cE
    cG
    coass
    3eqtr3g
    coeq2d
    cD
    cE
    @1
    coass
    cD
    cF
    @3
    coass
    3eqtr4g
end
