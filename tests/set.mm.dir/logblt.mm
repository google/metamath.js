include "c2.mm"
include "cuz.mm"
include "cfv.mm"
include "wcel.mm"
include "crp.mm"
include "w3a.mm"
include "clog.mm"
include "clt.mm"
include "wbr.mm"
include "cdiv.mm"
include "co.mm"
include "clogb.mm"
include "simp2.mm"
include "relogcld.mm"
include "simp3.mm"
include "cz.mm"
include "simp1.mm"
include "eluzelz.mm"
include "syl.mm"
include "zred.mm"
include "c1.mm"
include "caddc.mm"
include "1z.mm"
include "1p1e2.mm"
include "fveq2i.mm"
include "syl6eleqr.mm"
include "eluzp1l.mm"
include "sylancr.mm"
include "rplogcld.mm"
include "ltdiv1d.mm"
include "wb.mm"
include "logltb.mm"
include "3adant1.mm"
include "wceq.mm"
include "relogbval.mm"
include "3adant3.mm"
include "3adant2.mm"
include "breq12d.mm"
include "3bitr4d.mm"

theorem logblt
  let cB: class B
  let cX: class X
  let cY: class Y


  assert |- ( ( B e. ( ZZ>= ` 2 ) /\ X e. RR+ /\ Y e. RR+ ) -> ( X < Y <-> ( B logb X ) < ( B logb Y ) ) )

  proof
    cB
    c2
    cuz
    cfv
    #
    wcel
    #
    cX
    crp
    wcel
    #
    cY
    crp
    wcel
    #
    w3a
    #
    cX
    clog
    cfv
    #
    cY
    clog
    cfv
    #
    clt
    wbr
    #
    @5
    cB
    clog
    cfv
    #
    cdiv
    co
    #
    @6
    @8
    cdiv
    co
    #
    clt
    wbr
    cX
    cY
    clt
    wbr
    #
    cB
    cX
    clogb
    co
    #
    cB
    cY
    clogb
    co
    #
    clt
    wbr
    @4
    @5
    @6
    @8
    @4
    cX
    @1
    @2
    @3
    simp2
    relogcld
    @4
    cY
    @1
    @2
    @3
    simp3
    relogcld
    @4
    cB
    @4
    cB
    @4
    @1
    cB
    cz
    wcel
    @1
    @2
    @3
    simp1
    #
    c2
    cB
    eluzelz
    syl
    zred
    @4
    c1
    cz
    wcel
    cB
    c1
    c1
    caddc
    co
    #
    cuz
    cfv
    #
    wcel
    c1
    cB
    clt
    wbr
    1z
    @4
    cB
    @0
    @16
    @14
    @15
    c2
    cuz
    1p1e2
    fveq2i
    syl6eleqr
    c1
    cB
    eluzp1l
    sylancr
    rplogcld
    ltdiv1d
    @2
    @3
    @11
    @7
    wb
    @1
    cX
    cY
    logltb
    3adant1
    @4
    @12
    @9
    @13
    @10
    clt
    @1
    @2
    @12
    @9
    wceq
    @3
    cB
    cX
    relogbval
    3adant3
    @1
    @3
    @13
    @10
    wceq
    @2
    cB
    cY
    relogbval
    3adant2
    breq12d
    3bitr4d
end
