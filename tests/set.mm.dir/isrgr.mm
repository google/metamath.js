include "wcel.mm"
include "wa.mm"
include "crgr.mm"
include "wbr.mm"
include "cxnn0.mm"
include "cv.mm"
include "cvtxdg.mm"
include "cfv.mm"
include "wceq.mm"
include "cvtx.mm"
include "wral.mm"
include "wb.mm"
include "eleq1.mm"
include "adantl.mm"
include "fveq2.mm"
include "adantr.mm"
include "fveq1d.mm"
include "simpr.mm"
include "eqeq12d.mm"
include "raleqbidv.mm"
include "anbi12d.mm"
include "df-rgr.mm"
include "brabga.mm"
include "fveq1i.mm"
include "eqeq1i.mm"
include "raleqbii.mm"
include "bicomi.mm"
include "a1i.mm"
include "anbi2d.mm"
include "bitrd.mm"

theorem isrgr
  let vv: setvar v
  let cD: class D
  let cG: class G
  let cK: class K
  let cV: class V
  let cW: class W
  let cZ: class Z
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
  assert |- ( ( G e. W /\ K e. Z ) -> ( G RegGraph K <-> ( K e. NN0* /\ A. v e. V ( D ` v ) = K ) ) )

  proof
    cG
    cW
    wcel
    cK
    cZ
    wcel
    wa
    #
    cG
    cK
    crgr
    wbr
    cK
    cxnn0
    wcel
    #
    vv
    cv
    #
    cG
    cvtxdg
    cfv
    #
    cfv
    #
    cK
    wceq
    #
    vv
    cG
    cvtx
    cfv
    #
    wral
    #
    wa
    #
    @1
    @2
    cD
    cfv
    #
    cK
    wceq
    #
    vv
    cV
    wral
    #
    wa
    vk
    cv
    #
    cxnn0
    wcel
    #
    @2
    vg
    cv
    #
    cvtxdg
    cfv
    #
    cfv
    #
    @12
    wceq
    #
    vv
    @14
    cvtx
    cfv
    #
    wral
    #
    wa
    @8
    vg
    vk
    cG
    cK
    crgr
    cW
    cZ
    @14
    cG
    wceq
    #
    @12
    cK
    wceq
    #
    wa
    #
    @13
    @1
    @19
    @7
    @21
    @13
    @1
    wb
    @20
    @12
    cK
    cxnn0
    eleq1
    adantl
    @22
    @17
    @5
    vv
    @18
    @6
    @20
    @18
    @6
    wceq
    @21
    @14
    cG
    cvtx
    fveq2
    adantr
    @22
    @16
    @4
    @12
    cK
    @20
    @16
    @4
    wceq
    @21
    @20
    @2
    @15
    @3
    @14
    cG
    cvtxdg
    fveq2
    fveq1d
    adantr
    @20
    @21
    simpr
    eqeq12d
    raleqbidv
    anbi12d
    vv
    vg
    vk
    df-rgr
    brabga
    @0
    @7
    @11
    @1
    @7
    @11
    wb
    @0
    @11
    @7
    @10
    @5
    vv
    cV
    @6
    isrgr.v
    @9
    @4
    cK
    @2
    cD
    @3
    isrgr.d
    fveq1i
    eqeq1i
    raleqbii
    bicomi
    a1i
    anbi2d
    bitrd
end
