include "wcel.mm"
include "w3a.mm"
include "wne.mm"
include "ccom.mm"
include "cfv.mm"
include "pmtr3ncomlem1.mm"
include "fveq1.mm"
include "necon3i.mm"
include "syl.mm"

theorem pmtr3ncomlem2
  let cD: class D
  let cT: class T
  let cF: class F
  let cG: class G
  let cV: class V
  let cX: class X
  let cY: class Y
  let cZ: class Z
  assume pmtr3ncom.t: |- T = ( pmTrsp ` D )
  assume pmtr3ncom.f: |- F = ( T ` { X , Y } )
  assume pmtr3ncom.g: |- G = ( T ` { Y , Z } )


  assert |- ( ( D e. V /\ ( X e. D /\ Y e. D /\ Z e. D ) /\ ( X =/= Y /\ X =/= Z /\ Y =/= Z ) ) -> ( G o. F ) =/= ( F o. G ) )

  proof
    cD
    cV
    wcel
    cX
    cD
    wcel
    cY
    cD
    wcel
    cZ
    cD
    wcel
    w3a
    cX
    cY
    wne
    cX
    cZ
    wne
    cY
    cZ
    wne
    w3a
    w3a
    cX
    cG
    cF
    ccom
    #
    cfv
    #
    cX
    cF
    cG
    ccom
    #
    cfv
    #
    wne
    @0
    @2
    wne
    cD
    cT
    cF
    cG
    cV
    cX
    cY
    cZ
    pmtr3ncom.t
    pmtr3ncom.f
    pmtr3ncom.g
    pmtr3ncomlem1
    @0
    @2
    @1
    @3
    cX
    @0
    @2
    fveq1
    necon3i
    syl
end
