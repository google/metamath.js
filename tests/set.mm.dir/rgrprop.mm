include "cvv.mm"
include "wcel.mm"
include "wa.mm"
include "crgr.mm"
include "wbr.mm"
include "cxnn0.mm"
include "cv.mm"
include "cfv.mm"
include "wceq.mm"
include "wral.mm"
include "cvtxdg.mm"
include "cvtx.mm"
include "copab.mm"
include "df-rgr.mm"
include "breqi.mm"
include "brabv.mm"
include "sylbi.mm"
include "isrgr.mm"
include "biimpd.mm"
include "mpcom.mm"

theorem rgrprop
  let vv: setvar v
  let cD: class D
  let cG: class G
  let cK: class K
  let cV: class V
  let vg: setvar g
  let vk: setvar k
  assume isrgr.v: |- V = ( Vtx ` G )
  assume isrgr.d: |- D = ( VtxDeg ` G )

  disjoint G v
  disjoint K v
  disjoint G g
  disjoint G k
  disjoint g k
  disjoint g v
  disjoint k v
  disjoint K g
  disjoint K k
  assert |- ( G RegGraph K -> ( K e. NN0* /\ A. v e. V ( D ` v ) = K ) )

  proof
    cG
    cvv
    wcel
    cK
    cvv
    wcel
    wa
    #
    cG
    cK
    crgr
    wbr
    #
    cK
    cxnn0
    wcel
    vv
    cv
    #
    cD
    cfv
    cK
    wceq
    vv
    cV
    wral
    wa
    #
    @1
    cG
    cK
    vk
    cv
    #
    cxnn0
    wcel
    @2
    vg
    cv
    #
    cvtxdg
    cfv
    cfv
    @4
    wceq
    vv
    @5
    cvtx
    cfv
    wral
    wa
    #
    vg
    vk
    copab
    #
    wbr
    @0
    cG
    cK
    crgr
    @7
    vv
    vg
    vk
    df-rgr
    breqi
    @6
    vg
    vk
    cG
    cK
    brabv
    sylbi
    @0
    @1
    @3
    vv
    cD
    cG
    cK
    cV
    cvv
    cvv
    isrgr.v
    isrgr.d
    isrgr
    biimpd
    mpcom
end
