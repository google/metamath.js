include "wceq.mm"
include "cdm.mm"
include "con0.mm"
include "wf.mm"
include "word.mm"
include "cv.mm"
include "wcel.mm"
include "cfv.mm"
include "wi.mm"
include "wral.mm"
include "w3a.mm"
include "wsmo.mm"
include "id.mm"
include "dmeq.mm"
include "feq12d.mm"
include "wb.mm"
include "ordeq.mm"
include "syl.mm"
include "fveq1.mm"
include "eleq12d.mm"
include "imbi2d.mm"
include "2ralbidv.mm"
include "raleqdv.mm"
include "ralbidv.mm"
include "3bitrd.mm"
include "3anbi123d.mm"
include "df-smo.mm"
include "3bitr4g.mm"

theorem smoeq
  let cA: class A
  let cB: class B
  let vx: setvar x
  let vy: setvar y


  assert |- ( A = B -> ( Smo A <-> Smo B ) )

  proof
    cA
    cB
    wceq
    #
    cA
    cdm
    #
    con0
    cA
    wf
    #
    @1
    word
    #
    vx
    cv
    #
    vy
    cv
    #
    wcel
    #
    @4
    cA
    cfv
    #
    @5
    cA
    cfv
    #
    wcel
    #
    wi
    #
    vy
    @1
    wral
    vx
    @1
    wral
    #
    w3a
    cB
    cdm
    #
    con0
    cB
    wf
    #
    @12
    word
    #
    @6
    @4
    cB
    cfv
    #
    @5
    cB
    cfv
    #
    wcel
    #
    wi
    #
    vy
    @12
    wral
    #
    vx
    @12
    wral
    #
    w3a
    cA
    wsmo
    cB
    wsmo
    @0
    @2
    @13
    @3
    @14
    @11
    @20
    @0
    @1
    @12
    con0
    cA
    cB
    @0
    id
    cA
    cB
    dmeq
    #
    feq12d
    @0
    @1
    @12
    wceq
    @3
    @14
    wb
    @21
    @1
    @12
    ordeq
    syl
    @0
    @11
    @18
    vy
    @1
    wral
    #
    vx
    @1
    wral
    @19
    vx
    @1
    wral
    @20
    @0
    @10
    @18
    vx
    vy
    @1
    @1
    @0
    @9
    @17
    @6
    @0
    @7
    @15
    @8
    @16
    @4
    cA
    cB
    fveq1
    @5
    cA
    cB
    fveq1
    eleq12d
    imbi2d
    2ralbidv
    @0
    @22
    @19
    vx
    @1
    @0
    @18
    vy
    @1
    @12
    @21
    raleqdv
    ralbidv
    @0
    @19
    vx
    @1
    @12
    @21
    raleqdv
    3bitrd
    3anbi123d
    vx
    vy
    cA
    df-smo
    vx
    vy
    cB
    df-smo
    3bitr4g
end
