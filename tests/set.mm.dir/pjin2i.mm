include "cpjh.mm"
include "cfv.mm"
include "ccom.mm"
include "wceq.mm"
include "wa.mm"
include "wss.mm"
include "eqss.mm"
include "pjss2coi.mm"
include "eqcom.mm"
include "bitri.mm"
include "anbi12i.mm"
include "bitr2i.mm"
include "fveq2.mm"
include "sylbi.mm"
include "pjidmcoi.mm"
include "coeq2.mm"
include "syl5eqr.mm"
include "syl6req.mm"
include "jca.mm"
include "impbii.mm"

theorem pjin2i
  let cG: class G
  let cH: class H
  assume pjin1.1: |- G e. CH
  assume pjin1.2: |- H e. CH


  assert |- ( ( ( projh ` G ) = ( ( projh ` G ) o. ( projh ` H ) ) /\ ( projh ` H ) = ( ( projh ` H ) o. ( projh ` G ) ) ) <-> ( projh ` G ) = ( projh ` H ) )

  proof
    cG
    cpjh
    cfv
    #
    @0
    cH
    cpjh
    cfv
    #
    ccom
    #
    wceq
    #
    @1
    @1
    @0
    ccom
    #
    wceq
    #
    wa
    #
    @0
    @1
    wceq
    #
    @6
    cG
    cH
    wceq
    #
    @7
    @8
    cG
    cH
    wss
    #
    cH
    cG
    wss
    #
    wa
    @6
    cG
    cH
    eqss
    @9
    @3
    @10
    @5
    @9
    @2
    @0
    wceq
    @3
    cG
    cH
    pjin1.1
    pjin1.2
    pjss2coi
    @2
    @0
    eqcom
    bitri
    @10
    @4
    @1
    wceq
    @5
    cH
    cG
    pjin1.2
    pjin1.1
    pjss2coi
    @4
    @1
    eqcom
    bitri
    anbi12i
    bitr2i
    cG
    cH
    cpjh
    fveq2
    sylbi
    @7
    @3
    @5
    @7
    @0
    @0
    @0
    ccom
    @2
    cG
    pjin1.1
    pjidmcoi
    @0
    @1
    @0
    coeq2
    syl5eqr
    @7
    @4
    @1
    @1
    ccom
    @1
    @0
    @1
    @1
    coeq2
    cH
    pjin1.2
    pjidmcoi
    syl6req
    jca
    impbii
end
