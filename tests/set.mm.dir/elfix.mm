include "cfix.mm"
include "wcel.mm"
include "cid.mm"
include "cin.mm"
include "cdm.mm"
include "cv.mm"
include "wceq.mm"
include "wbr.mm"
include "wa.mm"
include "wex.mm"
include "df-fix.mm"
include "eleq2i.mm"
include "eldm.mm"
include "brin.mm"
include "ancom.mm"
include "vex.mm"
include "ideq.mm"
include "eqcom.mm"
include "bitri.mm"
include "anbi1i.mm"
include "3bitri.mm"
include "exbii.mm"
include "breq2.mm"
include "ceqsexv.mm"

theorem elfix
  let cA: class A
  let cR: class R
  let vx: setvar x
  assume elfix.1: |- A e. _V


  assert |- ( A e. Fix R <-> A R A )

  proof
    cA
    cR
    cfix
    #
    wcel
    cA
    cR
    cid
    cin
    #
    cdm
    #
    wcel
    #
    vx
    cv
    #
    cA
    wceq
    #
    cA
    @4
    cR
    wbr
    #
    wa
    #
    vx
    wex
    #
    cA
    cA
    cR
    wbr
    #
    @0
    @2
    cA
    cR
    df-fix
    eleq2i
    @3
    cA
    @4
    @1
    wbr
    #
    vx
    wex
    @8
    vx
    cA
    @1
    elfix.1
    eldm
    @10
    @7
    vx
    @10
    @6
    cA
    @4
    cid
    wbr
    #
    wa
    @11
    @6
    wa
    @7
    cA
    @4
    cR
    cid
    brin
    @6
    @11
    ancom
    @11
    @5
    @6
    @11
    cA
    @4
    wceq
    @5
    cA
    @4
    vx
    vex
    ideq
    cA
    @4
    eqcom
    bitri
    anbi1i
    3bitri
    exbii
    bitri
    @6
    @9
    vx
    cA
    elfix.1
    @4
    cA
    cA
    cR
    breq2
    ceqsexv
    3bitri
end
