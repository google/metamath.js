include "cc.mm"
include "wcel.mm"
include "cpi.mm"
include "c2.mm"
include "cdiv.mm"
include "co.mm"
include "cacos.mm"
include "cfv.mm"
include "cmin.mm"
include "ccos.mm"
include "casin.mm"
include "csin.mm"
include "c1.mm"
include "cexp.mm"
include "csqrt.mm"
include "acosval.mm"
include "oveq2d.mm"
include "wceq.mm"
include "picn.mm"
include "halfcl.mm"
include "ax-mp.mm"
include "asincl.mm"
include "nncan.mm"
include "sylancr.mm"
include "eqtrd.mm"
include "fveq2d.mm"
include "acoscl.mm"
include "coshalfpim.mm"
include "syl.mm"
include "cosasin.mm"
include "3eqtr3d.mm"

theorem sinacos
  let cA: class A


  assert |- ( A e. CC -> ( sin ` ( arccos ` A ) ) = ( sqrt ` ( 1 - ( A ^ 2 ) ) ) )

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
    cacos
    cfv
    #
    cmin
    co
    #
    ccos
    cfv
    #
    cA
    casin
    cfv
    #
    ccos
    cfv
    @2
    csin
    cfv
    #
    c1
    cA
    c2
    cexp
    co
    cmin
    co
    csqrt
    cfv
    @0
    @3
    @5
    ccos
    @0
    @3
    @1
    @1
    @5
    cmin
    co
    #
    cmin
    co
    #
    @5
    @0
    @2
    @7
    @1
    cmin
    cA
    acosval
    oveq2d
    @0
    @1
    cc
    wcel
    #
    @5
    cc
    wcel
    @8
    @5
    wceq
    cpi
    cc
    wcel
    @9
    picn
    cpi
    halfcl
    ax-mp
    cA
    asincl
    @1
    @5
    nncan
    sylancr
    eqtrd
    fveq2d
    @0
    @2
    cc
    wcel
    @4
    @6
    wceq
    cA
    acoscl
    @2
    coshalfpim
    syl
    cA
    cosasin
    3eqtr3d
end
