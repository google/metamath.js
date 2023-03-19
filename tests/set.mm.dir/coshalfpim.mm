include "cc.mm"
include "wcel.mm"
include "cpi.mm"
include "c2.mm"
include "cdiv.mm"
include "co.mm"
include "cmin.mm"
include "ccos.mm"
include "cfv.mm"
include "cmul.mm"
include "csin.mm"
include "caddc.mm"
include "cc0.mm"
include "wceq.mm"
include "picn.mm"
include "2cn.mm"
include "2ne0.mm"
include "divcli.mm"
include "cossub.mm"
include "mpan.mm"
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
include "addid2d.mm"
include "3eqtrd.mm"

theorem coshalfpim
  let cA: class A


  assert |- ( A e. CC -> ( cos ` ( ( _pi / 2 ) - A ) ) = ( sin ` A ) )

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
    cmin
    co
    ccos
    cfv
    #
    @1
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
    caddc
    co
    #
    cc0
    @7
    caddc
    co
    @7
    @1
    cc
    wcel
    @0
    @2
    @9
    wceq
    cpi
    c2
    picn
    2cn
    2ne0
    divcli
    @1
    cA
    cossub
    mpan
    @0
    @5
    cc0
    @8
    @7
    caddc
    @0
    @5
    cc0
    @4
    cmul
    co
    cc0
    @3
    cc0
    @4
    cmul
    coshalfpi
    oveq1i
    @0
    @4
    cA
    coscl
    mul02d
    syl5eq
    @0
    @8
    c1
    @7
    cmul
    co
    @7
    @6
    c1
    @7
    cmul
    sinhalfpi
    oveq1i
    @0
    @7
    cA
    sincl
    #
    mulid2d
    syl5eq
    oveq12d
    @0
    @7
    @10
    addid2d
    3eqtrd
end
