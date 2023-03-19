include "cc.mm"
include "wcel.mm"
include "cpi.mm"
include "c2.mm"
include "cdiv.mm"
include "co.mm"
include "caddc.mm"
include "csin.mm"
include "cfv.mm"
include "cc0.mm"
include "wceq.mm"
include "cz.mm"
include "ccos.mm"
include "c1.mm"
include "wb.mm"
include "picn.mm"
include "a1i.mm"
include "halfcld.mm"
include "id.mm"
include "addcld.mm"
include "sineq0.mm"
include "syl.mm"
include "sinhalfpip.mm"
include "eqeq1d.mm"
include "wne.mm"
include "pire.mm"
include "pipos.mm"
include "gt0ne0ii.mm"
include "divdird.mm"
include "2cnd.mm"
include "2ne0.mm"
include "divdiv32d.mm"
include "dividd.mm"
include "oveq1d.mm"
include "eqtrd.mm"
include "1cnd.mm"
include "divcld.mm"
include "addcomd.mm"
include "3eqtrd.mm"
include "eleq1d.mm"
include "3bitr3d.mm"

theorem coseq0
  let cA: class A
  let vk: setvar k
  let vx: setvar x


  assert |- ( A e. CC -> ( ( cos ` A ) = 0 <-> ( ( A / _pi ) + ( 1 / 2 ) ) e. ZZ ) )

  proof
    cA
    cc
    wcel
    #
    cpi
    c2
    cdiv
    co
    #
    cA
    caddc
    co
    #
    csin
    cfv
    #
    cc0
    wceq
    #
    @2
    cpi
    cdiv
    co
    #
    cz
    wcel
    #
    cA
    ccos
    cfv
    #
    cc0
    wceq
    cA
    cpi
    cdiv
    co
    #
    c1
    c2
    cdiv
    co
    #
    caddc
    co
    #
    cz
    wcel
    @0
    @2
    cc
    wcel
    @4
    @6
    wb
    @0
    @1
    cA
    @0
    cpi
    cpi
    cc
    wcel
    @0
    picn
    a1i
    #
    halfcld
    #
    @0
    id
    #
    addcld
    @2
    sineq0
    syl
    @0
    @3
    @7
    cc0
    cA
    sinhalfpip
    eqeq1d
    @0
    @5
    @10
    cz
    @0
    @5
    @1
    cpi
    cdiv
    co
    #
    @8
    caddc
    co
    @9
    @8
    caddc
    co
    @10
    @0
    @1
    cA
    cpi
    @12
    @13
    @11
    cpi
    cc0
    wne
    @0
    cpi
    pire
    pipos
    gt0ne0ii
    a1i
    #
    divdird
    @0
    @14
    @9
    @8
    caddc
    @0
    @14
    cpi
    cpi
    cdiv
    co
    #
    c2
    cdiv
    co
    @9
    @0
    cpi
    c2
    cpi
    @11
    @0
    2cnd
    @11
    c2
    cc0
    wne
    @0
    2ne0
    a1i
    @15
    divdiv32d
    @0
    @16
    c1
    c2
    cdiv
    @0
    cpi
    @11
    @15
    dividd
    oveq1d
    eqtrd
    oveq1d
    @0
    @9
    @8
    @0
    c1
    @0
    1cnd
    halfcld
    @0
    cA
    cpi
    @13
    @11
    @15
    divcld
    addcomd
    3eqtrd
    eleq1d
    3bitr3d
end
