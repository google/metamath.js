include "cc.mm"
include "wcel.mm"
include "cpi.mm"
include "c2.mm"
include "cdiv.mm"
include "co.mm"
include "cmin.mm"
include "csin.mm"
include "cfv.mm"
include "ccos.mm"
include "cmul.mm"
include "cc0.mm"
include "wceq.mm"
include "picn.mm"
include "2cn.mm"
include "2ne0.mm"
include "divcli.mm"
include "sinsub.mm"
include "mpan.mm"
include "c1.mm"
include "sinhalfpi.mm"
include "oveq1i.mm"
include "coscl.mm"
include "mulid2d.mm"
include "syl5eq.mm"
include "coshalfpi.mm"
include "sincl.mm"
include "mul02d.mm"
include "oveq12d.mm"
include "subid1d.mm"
include "3eqtrd.mm"

theorem sinhalfpim
  let cA: class A


  assert |- ( A e. CC -> ( sin ` ( ( _pi / 2 ) - A ) ) = ( cos ` A ) )

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
    csin
    cfv
    #
    @1
    csin
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
    ccos
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
    @4
    cc0
    cmin
    co
    @4
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
    sinsub
    mpan
    @0
    @5
    @4
    @8
    cc0
    cmin
    @0
    @5
    c1
    @4
    cmul
    co
    @4
    @3
    c1
    @4
    cmul
    sinhalfpi
    oveq1i
    @0
    @4
    cA
    coscl
    #
    mulid2d
    syl5eq
    @0
    @8
    cc0
    @7
    cmul
    co
    cc0
    @6
    cc0
    @7
    cmul
    coshalfpi
    oveq1i
    @0
    @7
    cA
    sincl
    mul02d
    syl5eq
    oveq12d
    @0
    @4
    @10
    subid1d
    3eqtrd
end
