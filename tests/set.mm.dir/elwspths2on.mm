include "cupgr.mm"
include "wcel.mm"
include "w3a.mm"
include "c2.mm"
include "cwwspthsnon.mm"
include "co.mm"
include "cv.mm"
include "cs3.mm"
include "wceq.mm"
include "wa.mm"
include "wrex.mm"
include "cwwlksnon.mm"
include "cspthson.mm"
include "cfv.mm"
include "wbr.mm"
include "wex.mm"
include "wspthnon.mm"
include "biimpi.mm"
include "wi.mm"
include "cwlks.mm"
include "chash.mm"
include "elwwlks2on.mm"
include "simpl.mm"
include "eleq1.mm"
include "biimpa.mm"
include "jca.mm"
include "ex.mm"
include "adantr.mm"
include "com12.mm"
include "reximdv.mm"
include "a1i13.mm"
include "com24.mm"
include "sylbid.mm"
include "impd.mm"
include "com23.mm"
include "mpdi.mm"
include "biimpar.mm"
include "a1i.mm"
include "rexlimdva.mm"
include "impbid.mm"

theorem elwspths2on
  let cA: class A
  let cC: class C
  let cG: class G
  let cV: class V
  let cW: class W
  let vb: setvar b
  let vf: setvar f
  assume elwwlks2on.v: |- V = ( Vtx ` G )

  disjoint A b
  disjoint C b
  disjoint G b
  disjoint V b
  disjoint W b
  disjoint A f
  disjoint b f
  disjoint C f
  disjoint G f
  disjoint W f
  disjoint V f
  assert |- ( ( G e. UPGraph /\ A e. V /\ C e. V ) -> ( W e. ( A ( 2 WSPathsNOn G ) C ) <-> E. b e. V ( W = <" A b C "> /\ <" A b C "> e. ( A ( 2 WSPathsNOn G ) C ) ) ) )

  proof
    cG
    cupgr
    wcel
    cA
    cV
    wcel
    cC
    cV
    wcel
    w3a
    #
    cW
    cA
    cC
    c2
    cG
    cwwspthsnon
    co
    co
    #
    wcel
    #
    cW
    cA
    vb
    cv
    #
    cC
    cs3
    #
    wceq
    #
    @4
    @1
    wcel
    #
    wa
    #
    vb
    cV
    wrex
    #
    @0
    @2
    cW
    cA
    cC
    c2
    cG
    cwwlksnon
    co
    co
    wcel
    #
    vf
    cv
    #
    cW
    cA
    cC
    cG
    cspthson
    cfv
    co
    wbr
    vf
    wex
    #
    wa
    #
    @8
    @2
    @12
    cA
    cC
    vf
    cG
    c2
    cW
    wspthnon
    biimpi
    @0
    @12
    @2
    @8
    @0
    @9
    @11
    @2
    @8
    wi
    #
    @0
    @9
    @5
    @10
    cW
    cG
    cwlks
    cfv
    wbr
    @10
    chash
    cfv
    c2
    wceq
    wa
    vf
    wex
    #
    wa
    #
    vb
    cV
    wrex
    #
    @11
    @13
    wi
    cA
    cC
    vf
    cG
    cV
    cW
    vb
    elwwlks2on.v
    elwwlks2on
    @0
    @2
    @11
    @16
    @8
    @0
    @2
    @11
    @16
    @8
    wi
    @2
    @15
    @7
    vb
    cV
    @15
    @2
    @7
    @5
    @2
    @7
    wi
    @14
    @5
    @2
    @7
    @5
    @2
    wa
    @5
    @6
    @5
    @2
    simpl
    @5
    @2
    @6
    cW
    @4
    @1
    eleq1
    #
    biimpa
    jca
    ex
    adantr
    com12
    reximdv
    a1i13
    com24
    sylbid
    impd
    com23
    mpdi
    @0
    @7
    @2
    vb
    cV
    @7
    @2
    wi
    @0
    @3
    cV
    wcel
    wa
    @5
    @2
    @6
    @17
    biimpar
    a1i
    rexlimdva
    impbid
end
