include "cc.mm"
include "wcel.mm"
include "cpi.mm"
include "cmin.mm"
include "co.mm"
include "csin.mm"
include "cfv.mm"
include "ccos.mm"
include "cmul.mm"
include "cneg.mm"
include "wceq.mm"
include "picn.mm"
include "sinsub.mm"
include "mpan2.mm"
include "cc0.mm"
include "c1.mm"
include "cospi.mm"
include "oveq2i.mm"
include "sincl.mm"
include "neg1cn.mm"
include "mulcom.mm"
include "mulm1.mm"
include "eqtrd.mm"
include "syl.mm"
include "syl5eq.mm"
include "sinpi.mm"
include "coscl.mm"
include "mul01d.mm"
include "oveq12d.mm"
include "negcld.mm"
include "subid1d.mm"

theorem sinmpi
  let cA: class A


  assert |- ( A e. CC -> ( sin ` ( A - _pi ) ) = -u ( sin ` A ) )

  proof
    cA
    cc
    wcel
    #
    cA
    cpi
    cmin
    co
    csin
    cfv
    #
    cA
    csin
    cfv
    #
    cpi
    ccos
    cfv
    #
    cmul
    co
    #
    cA
    ccos
    cfv
    #
    cpi
    csin
    cfv
    #
    cmul
    co
    #
    cmin
    co
    #
    @2
    cneg
    #
    @0
    cpi
    cc
    wcel
    @1
    @8
    wceq
    picn
    cA
    cpi
    sinsub
    mpan2
    @0
    @8
    @9
    cc0
    cmin
    co
    @9
    @0
    @4
    @9
    @7
    cc0
    cmin
    @0
    @4
    @2
    c1
    cneg
    #
    cmul
    co
    #
    @9
    @3
    @10
    @2
    cmul
    cospi
    oveq2i
    @0
    @2
    cc
    wcel
    #
    @11
    @9
    wceq
    cA
    sincl
    #
    @12
    @11
    @10
    @2
    cmul
    co
    #
    @9
    @12
    @10
    cc
    wcel
    @11
    @14
    wceq
    neg1cn
    @2
    @10
    mulcom
    mpan2
    @2
    mulm1
    eqtrd
    syl
    syl5eq
    @0
    @7
    @5
    cc0
    cmul
    co
    cc0
    @6
    cc0
    @5
    cmul
    sinpi
    oveq2i
    @0
    @5
    cA
    coscl
    mul01d
    syl5eq
    oveq12d
    @0
    @9
    @0
    @2
    @13
    negcld
    subid1d
    eqtrd
    eqtrd
end
