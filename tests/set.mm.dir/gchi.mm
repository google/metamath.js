include "cgch.mm"
include "wcel.mm"
include "csdm.mm"
include "wbr.mm"
include "cpw.mm"
include "cfn.mm"
include "wa.mm"
include "cv.mm"
include "wn.mm"
include "wal.mm"
include "wex.mm"
include "cvv.mm"
include "relsdom.mm"
include "brrelexi.mm"
include "adantl.mm"
include "wceq.mm"
include "breq2.mm"
include "breq1.mm"
include "anbi12d.mm"
include "spcegv.mm"
include "mpcom.mm"
include "df-ex.mm"
include "sylib.mm"
include "wo.mm"
include "elgch.mm"
include "ibi.mm"
include "orcomd.mm"
include "ord.mm"
include "syl5.mm"
include "3impib.mm"

theorem gchi
  let cA: class A
  let cB: class B
  let vx: setvar x
  let vy: setvar y


  assert |- ( ( A e. GCH /\ A ~< B /\ B ~< ~P A ) -> A e. Fin )

  proof
    cA
    cgch
    wcel
    #
    cA
    cB
    csdm
    wbr
    #
    cB
    cA
    cpw
    #
    csdm
    wbr
    #
    cA
    cfn
    wcel
    #
    @1
    @3
    wa
    #
    cA
    vx
    cv
    #
    csdm
    wbr
    #
    @6
    @2
    csdm
    wbr
    #
    wa
    #
    wn
    vx
    wal
    #
    wn
    #
    @0
    @4
    @5
    @9
    vx
    wex
    #
    @11
    cB
    cvv
    wcel
    #
    @5
    @12
    @3
    @13
    @1
    cB
    @2
    csdm
    relsdom
    brrelexi
    adantl
    @9
    @5
    vx
    cB
    cvv
    @6
    cB
    wceq
    @7
    @1
    @8
    @3
    @6
    cB
    cA
    csdm
    breq2
    @6
    cB
    @2
    csdm
    breq1
    anbi12d
    spcegv
    mpcom
    @9
    vx
    df-ex
    sylib
    @0
    @10
    @4
    @0
    @4
    @10
    @0
    @4
    @10
    wo
    vx
    cA
    cgch
    elgch
    ibi
    orcomd
    ord
    syl5
    3impib
end
