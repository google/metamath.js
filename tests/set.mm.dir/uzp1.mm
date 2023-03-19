include "cuz.mm"
include "cfv.mm"
include "wcel.mm"
include "wceq.mm"
include "c1.mm"
include "cmin.mm"
include "co.mm"
include "wo.mm"
include "caddc.mm"
include "uzm1.mm"
include "eluzp1p1.mm"
include "cc.mm"
include "eluzelcn.mm"
include "ax-1cn.mm"
include "npcan.mm"
include "sylancl.mm"
include "eleq1d.mm"
include "syl5ib.mm"
include "orim2d.mm"
include "mpd.mm"

theorem uzp1
  let cM: class M
  let cN: class N


  assert |- ( N e. ( ZZ>= ` M ) -> ( N = M \/ N e. ( ZZ>= ` ( M + 1 ) ) ) )

  proof
    cN
    cM
    cuz
    cfv
    #
    wcel
    #
    cN
    cM
    wceq
    #
    cN
    c1
    cmin
    co
    #
    @0
    wcel
    #
    wo
    @2
    cN
    cM
    c1
    caddc
    co
    cuz
    cfv
    #
    wcel
    #
    wo
    cM
    cN
    uzm1
    @1
    @4
    @6
    @2
    @4
    @3
    c1
    caddc
    co
    #
    @5
    wcel
    @1
    @6
    cM
    @3
    eluzp1p1
    @1
    @7
    cN
    @5
    @1
    cN
    cc
    wcel
    c1
    cc
    wcel
    @7
    cN
    wceq
    cM
    cN
    eluzelcn
    ax-1cn
    cN
    c1
    npcan
    sylancl
    eleq1d
    syl5ib
    orim2d
    mpd
end
