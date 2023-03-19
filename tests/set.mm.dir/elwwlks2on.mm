include "c2.mm"
include "cwwlksnon.mm"
include "co.mm"
include "wcel.mm"
include "cv.mm"
include "cs3.mm"
include "wceq.mm"
include "wa.mm"
include "wrex.mm"
include "cupgr.mm"
include "w3a.mm"
include "cwlks.mm"
include "cfv.mm"
include "wbr.mm"
include "chash.mm"
include "wex.mm"
include "elwwlks2ons3.mm"
include "s3wwlks2on.mm"
include "wb.mm"
include "breq2.mm"
include "eqcoms.mm"
include "anbi1d.mm"
include "exbidv.mm"
include "sylan9bb.mm"
include "pm5.32da.mm"
include "rexbidv.mm"
include "syl5bb.mm"

theorem elwwlks2on
  let cA: class A
  let cC: class C
  let vf: setvar f
  let cG: class G
  let cV: class V
  let cW: class W
  let vb: setvar b
  assume elwwlks2on.v: |- V = ( Vtx ` G )

  disjoint A b
  disjoint A f
  disjoint b f
  disjoint C b
  disjoint C f
  disjoint G b
  disjoint G f
  disjoint V b
  disjoint W b
  disjoint W f
  assert |- ( ( G e. UPGraph /\ A e. V /\ C e. V ) -> ( W e. ( A ( 2 WWalksNOn G ) C ) <-> E. b e. V ( W = <" A b C "> /\ E. f ( f ( Walks ` G ) W /\ ( # ` f ) = 2 ) ) ) )

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
    @2
    @0
    wcel
    #
    wa
    #
    vb
    cV
    wrex
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
    @3
    vf
    cv
    #
    cW
    cG
    cwlks
    cfv
    #
    wbr
    #
    @7
    chash
    cfv
    c2
    wceq
    #
    wa
    #
    vf
    wex
    #
    wa
    #
    vb
    cV
    wrex
    cA
    cC
    cG
    cV
    cW
    vb
    elwwlks2on.v
    elwwlks2ons3
    @6
    @5
    @13
    vb
    cV
    @6
    @3
    @4
    @12
    @6
    @4
    @7
    @2
    @8
    wbr
    #
    @10
    wa
    #
    vf
    wex
    @3
    @12
    cA
    @1
    cC
    vf
    cG
    cV
    elwwlks2on.v
    s3wwlks2on
    @3
    @15
    @11
    vf
    @3
    @14
    @9
    @10
    @14
    @9
    wb
    @2
    cW
    @2
    cW
    @7
    @8
    breq2
    eqcoms
    anbi1d
    exbidv
    sylan9bb
    pm5.32da
    rexbidv
    syl5bb
end
