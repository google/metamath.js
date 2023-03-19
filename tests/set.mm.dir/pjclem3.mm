include "cpjh.mm"
include "cfv.mm"
include "ccom.mm"
include "wceq.mm"
include "chil.mm"
include "chod.mm"
include "co.mm"
include "cort.mm"
include "chio.mm"
include "df-iop.mm"
include "coeq2i.mm"
include "pjfi.mm"
include "hoid1i.mm"
include "eqtr3i.mm"
include "hoid1ri.mm"
include "coeq1i.mm"
include "3eqtr2i.mm"
include "oveq1i.mm"
include "oveq2.mm"
include "syl5eq.mm"
include "helch.mm"
include "pjddii.mm"
include "hocsubdiri.mm"
include "3eqtr4g.mm"
include "pjoci.mm"
include "3eqtr3g.mm"

theorem pjclem3
  let cG: class G
  let cH: class H
  let vx: setvar x
  let vy: setvar y
  assume pjclem1.1: |- G e. CH
  assume pjclem1.2: |- H e. CH


  assert |- ( ( ( projh ` G ) o. ( projh ` H ) ) = ( ( projh ` H ) o. ( projh ` G ) ) -> ( ( projh ` G ) o. ( projh ` ( _|_ ` H ) ) ) = ( ( projh ` ( _|_ ` H ) ) o. ( projh ` G ) ) )

  proof
    cG
    cpjh
    cfv
    #
    cH
    cpjh
    cfv
    #
    ccom
    #
    @1
    @0
    ccom
    #
    wceq
    #
    @0
    chil
    cpjh
    cfv
    #
    @1
    chod
    co
    #
    ccom
    #
    @6
    @0
    ccom
    #
    @0
    cH
    cort
    cfv
    cpjh
    cfv
    #
    ccom
    @9
    @0
    ccom
    @4
    @0
    @5
    ccom
    #
    @2
    chod
    co
    #
    @5
    @0
    ccom
    #
    @3
    chod
    co
    #
    @7
    @8
    @4
    @11
    @12
    @2
    chod
    co
    @13
    @10
    @12
    @2
    chod
    @10
    @0
    chio
    @0
    ccom
    @12
    @0
    chio
    ccom
    @10
    @0
    chio
    @5
    @0
    df-iop
    coeq2i
    @0
    cG
    pjclem1.1
    pjfi
    #
    hoid1i
    eqtr3i
    @0
    @14
    hoid1ri
    chio
    @5
    @0
    df-iop
    coeq1i
    3eqtr2i
    oveq1i
    @2
    @3
    @12
    chod
    oveq2
    syl5eq
    @5
    @1
    cG
    pjclem1.1
    chil
    helch
    pjfi
    #
    cH
    pjclem1.2
    pjfi
    #
    pjddii
    @5
    @1
    @0
    @15
    @16
    @14
    hocsubdiri
    3eqtr4g
    @6
    @9
    @0
    cH
    pjclem1.2
    pjoci
    #
    coeq2i
    @6
    @9
    @0
    @17
    coeq1i
    3eqtr3g
end
