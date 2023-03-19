include "wdfat.mm"
include "cdm.mm"
include "wcel.mm"
include "csn.mm"
include "cres.mm"
include "wfun.mm"
include "wa.mm"
include "cv.mm"
include "wbr.mm"
include "weu.mm"
include "wral.mm"
include "df-dfat.mm"
include "wrel.mm"
include "relres.mm"
include "dffun8.mm"
include "mpbiran.mm"
include "anbi2i.mm"
include "wb.mm"
include "vex.mm"
include "brres.mm"
include "a1i.mm"
include "eubidv.mm"
include "ralbidv.mm"
include "eldmressnsn.mm"
include "eldmressn.mm"
include "wceq.mm"
include "breq1.mm"
include "anbi1d.mm"
include "velsn.mm"
include "biimpri.mm"
include "biantrud.mm"
include "bitr4d.mm"
include "ralbinrald.mm"
include "bitrd.mm"
include "pm5.32i.mm"
include "3bitri.mm"

theorem dfdfat2
  let vy: setvar y
  let cA: class A
  let cF: class F
  let vx: setvar x
  let vk: setvar k

  disjoint A y
  disjoint F y
  disjoint x y
  disjoint A x
  disjoint F x
  disjoint k x
  assert |- ( F defAt A <-> ( A e. dom F /\ E! y A F y ) )

  proof
    cA
    cF
    wdfat
    cA
    cF
    cdm
    wcel
    #
    cF
    cA
    csn
    #
    cres
    #
    wfun
    #
    wa
    @0
    vx
    cv
    #
    vy
    cv
    #
    @2
    wbr
    #
    vy
    weu
    #
    vx
    @2
    cdm
    #
    wral
    #
    wa
    @0
    cA
    @5
    cF
    wbr
    #
    vy
    weu
    #
    wa
    cA
    cF
    df-dfat
    @3
    @9
    @0
    @3
    @2
    wrel
    @9
    cF
    @1
    relres
    vx
    vy
    @2
    dffun8
    mpbiran
    anbi2i
    @0
    @9
    @11
    @0
    @9
    @4
    @5
    cF
    wbr
    #
    @4
    @1
    wcel
    #
    wa
    #
    vy
    weu
    #
    vx
    @8
    wral
    @11
    @0
    @7
    @15
    vx
    @8
    @0
    @6
    @14
    vy
    @6
    @14
    wb
    @0
    @4
    @5
    cF
    @1
    vy
    vex
    brres
    a1i
    eubidv
    ralbidv
    @0
    @15
    @11
    vx
    @8
    cA
    cA
    cF
    eldmressnsn
    cA
    @4
    cF
    eldmressn
    @4
    cA
    wceq
    #
    @14
    @10
    vy
    @16
    @14
    @10
    @13
    wa
    @10
    @16
    @12
    @10
    @13
    @4
    cA
    @5
    cF
    breq1
    anbi1d
    @16
    @13
    @10
    @13
    @16
    vx
    cA
    velsn
    biimpri
    biantrud
    bitr4d
    eubidv
    ralbinrald
    bitrd
    pm5.32i
    3bitri
end
