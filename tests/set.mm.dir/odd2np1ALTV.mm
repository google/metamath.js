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
include "wa.mm"
include "codd.mm"
include "ibar.mm"
include "wb.mm"
include "eqcom.mm"
include "a1i.mm"
include "rexbidv.mm"
include "eqeq1.mm"
include "dfodd6.mm"
include "elrab2.mm"
include "3bitr4rd.mm"

theorem odd2np1ALTV
  let vn: setvar n
  let cN: class N
  let vz: setvar z
  let vk: setvar k
  let vx: setvar x

  disjoint N n
  disjoint N z
  disjoint n z
  disjoint k x
  assert |- ( N e. ZZ -> ( N e. Odd <-> E. n e. ZZ ( ( 2 x. n ) + 1 ) = N ) )

  proof
    cN
    cz
    wcel
    #
    cN
    c2
    vn
    cv
    cmul
    co
    c1
    caddc
    co
    #
    wceq
    #
    vn
    cz
    wrex
    #
    @0
    @3
    wa
    #
    @1
    cN
    wceq
    #
    vn
    cz
    wrex
    cN
    codd
    wcel
    #
    @0
    @3
    ibar
    @0
    @5
    @2
    vn
    cz
    @5
    @2
    wb
    @0
    @1
    cN
    eqcom
    a1i
    rexbidv
    @6
    @4
    wb
    @0
    vz
    cv
    #
    @1
    wceq
    #
    vn
    cz
    wrex
    @3
    vz
    cN
    cz
    codd
    @7
    cN
    wceq
    @8
    @2
    vn
    cz
    @7
    cN
    @1
    eqeq1
    rexbidv
    vz
    vn
    dfodd6
    elrab2
    a1i
    3bitr4rd
end
