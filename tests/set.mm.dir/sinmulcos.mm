include "cc.mm"
include "wcel.mm"
include "wa.mm"
include "caddc.mm"
include "co.mm"
include "csin.mm"
include "cfv.mm"
include "cmin.mm"
include "c2.mm"
include "cdiv.mm"
include "ccos.mm"
include "cmul.mm"
include "simpl.mm"
include "sincld.mm"
include "wf.mm"
include "cosf.mm"
include "a1i.mm"
include "ffvelrnda.mm"
include "mulcld.mm"
include "coscld.mm"
include "sinf.mm"
include "ppncand.mm"
include "sinadd.mm"
include "sinsub.mm"
include "oveq12d.mm"
include "2timesd.mm"
include "3eqtr4d.mm"
include "oveq1d.mm"
include "2cnd.mm"
include "cc0.mm"
include "wne.mm"
include "2ne0.mm"
include "divcan3d.mm"
include "eqtr2d.mm"

theorem sinmulcos
  let cA: class A
  let cB: class B
  let vk: setvar k
  let vx: setvar x


  assert |- ( ( A e. CC /\ B e. CC ) -> ( ( sin ` A ) x. ( cos ` B ) ) = ( ( ( sin ` ( A + B ) ) + ( sin ` ( A - B ) ) ) / 2 ) )

  proof
    cA
    cc
    wcel
    #
    cB
    cc
    wcel
    #
    wa
    #
    cA
    cB
    caddc
    co
    csin
    cfv
    #
    cA
    cB
    cmin
    co
    csin
    cfv
    #
    caddc
    co
    #
    c2
    cdiv
    co
    c2
    cA
    csin
    cfv
    #
    cB
    ccos
    cfv
    #
    cmul
    co
    #
    cmul
    co
    #
    c2
    cdiv
    co
    @8
    @2
    @5
    @9
    c2
    cdiv
    @2
    @8
    cA
    ccos
    cfv
    #
    cB
    csin
    cfv
    #
    cmul
    co
    #
    caddc
    co
    #
    @8
    @12
    cmin
    co
    #
    caddc
    co
    @8
    @8
    caddc
    co
    @5
    @9
    @2
    @8
    @12
    @8
    @2
    @6
    @7
    @2
    cA
    @0
    @1
    simpl
    #
    sincld
    @0
    cc
    cc
    cB
    ccos
    cc
    cc
    ccos
    wf
    @0
    cosf
    a1i
    ffvelrnda
    mulcld
    #
    @2
    @10
    @11
    @2
    cA
    @15
    coscld
    @0
    cc
    cc
    cB
    csin
    cc
    cc
    csin
    wf
    @0
    sinf
    a1i
    ffvelrnda
    mulcld
    @16
    ppncand
    @2
    @3
    @13
    @4
    @14
    caddc
    cA
    cB
    sinadd
    cA
    cB
    sinsub
    oveq12d
    @2
    @8
    @16
    2timesd
    3eqtr4d
    oveq1d
    @2
    @8
    c2
    @16
    @2
    2cnd
    c2
    cc0
    wne
    @2
    2ne0
    a1i
    divcan3d
    eqtr2d
end
