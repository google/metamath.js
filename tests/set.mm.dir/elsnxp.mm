include "wcel.mm"
include "csn.mm"
include "cxp.mm"
include "cv.mm"
include "cop.mm"
include "wceq.mm"
include "wrex.mm"
include "wa.mm"
include "wex.mm"
include "elxp.mm"
include "df-rex.mm"
include "an13.mm"
include "exbii.mm"
include "bitr4i.mm"
include "elsni.mm"
include "opeq1d.mm"
include "eqeq2d.mm"
include "biimpa.mm"
include "reximi.mm"
include "sylbir.mm"
include "exlimiv.mm"
include "sylbi.mm"
include "snidg.mm"
include "opelxpi.mm"
include "sylan.mm"
include "eleq1.mm"
include "syl5ibrcom.mm"
include "rexlimdva.mm"
include "impbid2.mm"

theorem elsnxp
  let vy: setvar y
  let cA: class A
  let cV: class V
  let cX: class X
  let cZ: class Z
  let vx: setvar x

  disjoint A y
  disjoint V y
  disjoint X y
  disjoint Z y
  disjoint A x
  disjoint x y
  disjoint X x
  disjoint Z x
  assert |- ( X e. V -> ( Z e. ( { X } X. A ) <-> E. y e. A Z = <. X , y >. ) )

  proof
    cX
    cV
    wcel
    #
    cZ
    cX
    csn
    #
    cA
    cxp
    #
    wcel
    #
    cZ
    cX
    vy
    cv
    #
    cop
    #
    wceq
    #
    vy
    cA
    wrex
    #
    @3
    cZ
    vx
    cv
    #
    @4
    cop
    #
    wceq
    #
    @8
    @1
    wcel
    #
    @4
    cA
    wcel
    #
    wa
    wa
    #
    vy
    wex
    #
    vx
    wex
    @7
    vx
    vy
    cZ
    @1
    cA
    elxp
    @14
    @7
    vx
    @14
    @11
    @10
    wa
    #
    vy
    cA
    wrex
    #
    @7
    @16
    @12
    @15
    wa
    #
    vy
    wex
    @14
    @15
    vy
    cA
    df-rex
    @13
    @17
    vy
    @10
    @11
    @12
    an13
    exbii
    bitr4i
    @15
    @6
    vy
    cA
    @11
    @10
    @6
    @11
    @9
    @5
    cZ
    @11
    @8
    cX
    @4
    @8
    cX
    elsni
    opeq1d
    eqeq2d
    biimpa
    reximi
    sylbir
    exlimiv
    sylbi
    @0
    @6
    @3
    vy
    cA
    @0
    @12
    wa
    @3
    @6
    @5
    @2
    wcel
    #
    @0
    cX
    @1
    wcel
    @12
    @18
    cX
    cV
    snidg
    cX
    @4
    @1
    cA
    opelxpi
    sylan
    cZ
    @5
    @2
    eleq1
    syl5ibrcom
    rexlimdva
    impbid2
end
