include "c2.mm"
include "cwwlksnon.mm"
include "co.mm"
include "wcel.mm"
include "cv.mm"
include "cs3.mm"
include "wceq.mm"
include "wa.mm"
include "wrex.mm"
include "c1.mm"
include "cfv.mm"
include "id.mm"
include "elwwlks2ons3im.mm"
include "anass.mm"
include "sylanbrc.mm"
include "simpr.mm"
include "wb.mm"
include "s3eq2.mm"
include "eqeq2.mm"
include "eleq1.mm"
include "anbi12d.mm"
include "syl.mm"
include "adantl.mm"
include "biimpac.mm"
include "jca.mm"
include "adantr.mm"
include "rspcedvd.mm"
include "eqcoms.mm"
include "biimpa.mm"
include "rexlimivw.mm"
include "impbii.mm"

theorem elwwlks2ons3
  let cA: class A
  let cC: class C
  let cG: class G
  let cV: class V
  let cW: class W
  let vb: setvar b
  assume wwlks2onv.v: |- V = ( Vtx ` G )

  disjoint A b
  disjoint C b
  disjoint G b
  disjoint V b
  disjoint W b
  assert |- ( W e. ( A ( 2 WWalksNOn G ) C ) <-> E. b e. V ( W = <" A b C "> /\ <" A b C "> e. ( A ( 2 WWalksNOn G ) C ) ) )

  proof
    cW
    cA
    cC
    c2
    cG
    cwwlksnon
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
    @3
    @0
    wcel
    #
    wa
    #
    vb
    cV
    wrex
    #
    @1
    @1
    cW
    cA
    c1
    cW
    cfv
    #
    cC
    cs3
    #
    wceq
    #
    wa
    #
    @8
    cV
    wcel
    #
    wa
    #
    @7
    @1
    @1
    @10
    @12
    wa
    @13
    @1
    id
    cA
    cC
    cG
    cV
    cW
    wwlks2onv.v
    elwwlks2ons3im
    @1
    @10
    @12
    anass
    sylanbrc
    @13
    @6
    @10
    @9
    @0
    wcel
    #
    wa
    #
    vb
    @8
    cV
    @11
    @12
    simpr
    @2
    @8
    wceq
    #
    @6
    @15
    wb
    #
    @13
    @16
    @3
    @9
    wceq
    #
    @17
    cA
    @2
    cC
    @8
    s3eq2
    @18
    @4
    @10
    @5
    @14
    @3
    @9
    cW
    eqeq2
    @3
    @9
    @0
    eleq1
    anbi12d
    syl
    adantl
    @11
    @15
    @12
    @11
    @10
    @14
    @1
    @10
    simpr
    @10
    @1
    @14
    cW
    @9
    @0
    eleq1
    biimpac
    jca
    adantr
    rspcedvd
    syl
    @6
    @1
    vb
    cV
    @4
    @5
    @1
    @5
    @1
    wb
    @3
    cW
    @3
    cW
    @0
    eleq1
    eqcoms
    biimpa
    rexlimivw
    impbii
end
