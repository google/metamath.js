include "cz.mm"
include "wcel.mm"
include "c2.mm"
include "cv.mm"
include "cmul.mm"
include "co.mm"
include "c1.mm"
include "caddc.mm"
include "wceq.mm"
include "wrex.mm"
include "cmin.mm"
include "cdvds.mm"
include "wbr.mm"
include "wn.mm"
include "wa.mm"
include "simpl.mm"
include "zcnd.mm"
include "1cnd.mm"
include "2cnd.mm"
include "simpr.mm"
include "mulcld.mm"
include "subadd2d.mm"
include "eqcom.mm"
include "mulcomd.mm"
include "eqeq1d.mm"
include "syl5bb.mm"
include "bitr3d.mm"
include "rexbidva.mm"
include "odd2np1.mm"
include "wb.mm"
include "2z.mm"
include "peano2zm.mm"
include "divides.mm"
include "sylancr.mm"
include "3bitr4d.mm"

theorem oddm1even
  let cN: class N
  let vk: setvar k
  let vn: setvar n
  let vx: setvar x
  let vy: setvar y


  assert |- ( N e. ZZ -> ( -. 2 || N <-> 2 || ( N - 1 ) ) )

  proof
    cN
    cz
    wcel
    #
    c2
    vn
    cv
    #
    cmul
    co
    #
    c1
    caddc
    co
    cN
    wceq
    #
    vn
    cz
    wrex
    @1
    c2
    cmul
    co
    #
    cN
    c1
    cmin
    co
    #
    wceq
    #
    vn
    cz
    wrex
    #
    c2
    cN
    cdvds
    wbr
    wn
    c2
    @5
    cdvds
    wbr
    #
    @0
    @3
    @6
    vn
    cz
    @0
    @1
    cz
    wcel
    #
    wa
    #
    @5
    @2
    wceq
    #
    @3
    @6
    @10
    cN
    c1
    @2
    @10
    cN
    @0
    @9
    simpl
    zcnd
    @10
    1cnd
    @10
    c2
    @1
    @10
    2cnd
    #
    @10
    @1
    @0
    @9
    simpr
    zcnd
    #
    mulcld
    subadd2d
    @11
    @2
    @5
    wceq
    @10
    @6
    @5
    @2
    eqcom
    @10
    @2
    @4
    @5
    @10
    c2
    @1
    @12
    @13
    mulcomd
    eqeq1d
    syl5bb
    bitr3d
    rexbidva
    vn
    cN
    odd2np1
    @0
    c2
    cz
    wcel
    @5
    cz
    wcel
    @8
    @7
    wb
    2z
    cN
    peano2zm
    vn
    c2
    @5
    divides
    sylancr
    3bitr4d
end
