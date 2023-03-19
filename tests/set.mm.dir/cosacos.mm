include "cc.mm"
include "wcel.mm"
include "cacos.mm"
include "cfv.mm"
include "ccos.mm"
include "cpi.mm"
include "c2.mm"
include "cdiv.mm"
include "co.mm"
include "casin.mm"
include "cmin.mm"
include "csin.mm"
include "acosval.mm"
include "fveq2d.mm"
include "wceq.mm"
include "asincl.mm"
include "coshalfpim.mm"
include "syl.mm"
include "sinasin.mm"
include "3eqtrd.mm"

theorem cosacos
  let cA: class A


  assert |- ( A e. CC -> ( cos ` ( arccos ` A ) ) = A )

  proof
    cA
    cc
    wcel
    #
    cA
    cacos
    cfv
    #
    ccos
    cfv
    cpi
    c2
    cdiv
    co
    cA
    casin
    cfv
    #
    cmin
    co
    #
    ccos
    cfv
    #
    @2
    csin
    cfv
    #
    cA
    @0
    @1
    @3
    ccos
    cA
    acosval
    fveq2d
    @0
    @2
    cc
    wcel
    @4
    @5
    wceq
    cA
    asincl
    @2
    coshalfpim
    syl
    cA
    sinasin
    3eqtrd
end
