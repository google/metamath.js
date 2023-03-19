include "cc.mm"
include "wcel.mm"
include "cpi.mm"
include "c2.mm"
include "cdiv.mm"
include "co.mm"
include "ccos.mm"
include "cfv.mm"
include "cmul.mm"
include "csin.mm"
include "cmin.mm"
include "cc0.mm"
include "caddc.mm"
include "cneg.mm"
include "coshalfpi.mm"
include "oveq1i.mm"
include "coscl.mm"
include "mul02d.mm"
include "syl5eq.mm"
include "c1.mm"
include "sinhalfpi.mm"
include "sincl.mm"
include "mulid2d.mm"
include "oveq12d.mm"
include "wceq.mm"
include "picn.mm"
include "2cn.mm"
include "2ne0.mm"
include "divcli.mm"
include "cosadd.mm"
include "mpan.mm"
include "df-neg.mm"
include "a1i.mm"
include "3eqtr4d.mm"

theorem coshalfpip
  let cA: class A


  assert |- ( A e. CC -> ( cos ` ( ( _pi / 2 ) + A ) ) = -u ( sin ` A ) )

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
    ccos
    cfv
    #
    cA
    ccos
    cfv
    #
    cmul
    co
    #
    @1
    csin
    cfv
    #
    cA
    csin
    cfv
    #
    cmul
    co
    #
    cmin
    co
    #
    cc0
    @6
    cmin
    co
    #
    @1
    cA
    caddc
    co
    ccos
    cfv
    #
    @6
    cneg
    #
    @0
    @4
    cc0
    @7
    @6
    cmin
    @0
    @4
    cc0
    @3
    cmul
    co
    cc0
    @2
    cc0
    @3
    cmul
    coshalfpi
    oveq1i
    @0
    @3
    cA
    coscl
    mul02d
    syl5eq
    @0
    @7
    c1
    @6
    cmul
    co
    @6
    @5
    c1
    @6
    cmul
    sinhalfpi
    oveq1i
    @0
    @6
    cA
    sincl
    mulid2d
    syl5eq
    oveq12d
    @1
    cc
    wcel
    @0
    @10
    @8
    wceq
    cpi
    c2
    picn
    2cn
    2ne0
    divcli
    @1
    cA
    cosadd
    mpan
    @11
    @9
    wceq
    @0
    @6
    df-neg
    a1i
    3eqtr4d
end
