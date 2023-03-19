include "chlt.mm"
include "wcel.mm"
include "wa.mm"
include "cv.mm"
include "cid.mm"
include "cres.mm"
include "wne.mm"
include "cfv.mm"
include "wceq.mm"
include "wi.mm"
include "wral.mm"
include "tendoid.mm"
include "adantrr.mm"
include "adantrl.mm"
include "eqtr4d.mm"
include "fveq2.mm"
include "eqeq12d.mm"
include "syl5ibrcom.mm"
include "ralrimivw.mm"
include "r19.26.mm"
include "wo.mm"
include "jaob.mm"
include "wb.mm"
include "exmidne.mm"
include "pm5.5.mm"
include "ax-mp.mm"
include "bitr3i.mm"
include "ralbii.mm"
include "tendoeq1.mm"
include "3expia.mm"
include "syl5bi.mm"
include "mpand.mm"
include "3impia.mm"

theorem tendoeq2
  let cB: class B
  let cT: class T
  let cU: class U
  let vf: setvar f
  let cE: class E
  let cH: class H
  let cK: class K
  let cV: class V
  let cW: class W
  assume tendoeq2.b: |- B = ( Base ` K )
  assume tendoeq2.h: |- H = ( LHyp ` K )
  assume tendoeq2.t: |- T = ( ( LTrn ` K ) ` W )
  assume tendoeq2.e: |- E = ( ( TEndo ` K ) ` W )

  disjoint E f
  disjoint H f
  disjoint K f
  disjoint T f
  disjoint W f
  disjoint U f
  disjoint V f
  assert |- ( ( ( K e. HL /\ W e. H ) /\ ( U e. E /\ V e. E ) /\ A. f e. T ( f =/= ( _I |` B ) -> ( U ` f ) = ( V ` f ) ) ) -> U = V )

  proof
    cK
    chlt
    wcel
    cW
    cH
    wcel
    wa
    #
    cU
    cE
    wcel
    #
    cV
    cE
    wcel
    #
    wa
    #
    vf
    cv
    #
    cid
    cB
    cres
    #
    wne
    #
    @4
    cU
    cfv
    #
    @4
    cV
    cfv
    #
    wceq
    #
    wi
    #
    vf
    cT
    wral
    #
    cU
    cV
    wceq
    #
    @0
    @3
    wa
    #
    @4
    @5
    wceq
    #
    @9
    wi
    #
    vf
    cT
    wral
    #
    @11
    @12
    @13
    @15
    vf
    cT
    @13
    @9
    @14
    @5
    cU
    cfv
    #
    @5
    cV
    cfv
    #
    wceq
    @13
    @17
    @5
    @18
    @0
    @1
    @17
    @5
    wceq
    @2
    cB
    cU
    cE
    cH
    cK
    cW
    tendoeq2.b
    tendoeq2.h
    tendoeq2.e
    tendoid
    adantrr
    @0
    @2
    @18
    @5
    wceq
    @1
    cB
    cV
    cE
    cH
    cK
    cW
    tendoeq2.b
    tendoeq2.h
    tendoeq2.e
    tendoid
    adantrl
    eqtr4d
    @14
    @7
    @17
    @8
    @18
    @4
    @5
    cU
    fveq2
    @4
    @5
    cV
    fveq2
    eqeq12d
    syl5ibrcom
    ralrimivw
    @16
    @11
    wa
    #
    @9
    vf
    cT
    wral
    #
    @13
    @12
    @19
    @15
    @10
    wa
    #
    vf
    cT
    wral
    @20
    @15
    @10
    vf
    cT
    r19.26
    @21
    @9
    vf
    cT
    @21
    @14
    @6
    wo
    #
    @9
    wi
    #
    @9
    @14
    @9
    @6
    jaob
    @22
    @23
    @9
    wb
    @4
    @5
    exmidne
    @22
    @9
    pm5.5
    ax-mp
    bitr3i
    ralbii
    bitr3i
    @0
    @3
    @20
    @12
    cT
    cU
    vf
    cE
    cH
    cK
    cV
    cW
    tendoeq2.h
    tendoeq2.t
    tendoeq2.e
    tendoeq1
    3expia
    syl5bi
    mpand
    3impia
end
