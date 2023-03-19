include "cz.mm"
include "wcel.mm"
include "c1.mm"
include "caddc.mm"
include "co.mm"
include "cuz.mm"
include "cfv.mm"
include "wa.mm"
include "cmin.mm"
include "wceq.mm"
include "cc.mm"
include "eluzelcn.mm"
include "ax-1cn.mm"
include "npcan.mm"
include "sylancl.mm"
include "adantl.mm"
include "eluzp1m1.mm"
include "peano2uz.mm"
include "syl.mm"
include "eqeltrrd.mm"

theorem peano2uzr
  let cM: class M
  let cN: class N


  assert |- ( ( M e. ZZ /\ N e. ( ZZ>= ` ( M + 1 ) ) ) -> N e. ( ZZ>= ` M ) )

  proof
    cM
    cz
    wcel
    #
    cN
    cM
    c1
    caddc
    co
    #
    cuz
    cfv
    wcel
    #
    wa
    #
    cN
    c1
    cmin
    co
    #
    c1
    caddc
    co
    #
    cN
    cM
    cuz
    cfv
    #
    @2
    @5
    cN
    wceq
    #
    @0
    @2
    cN
    cc
    wcel
    c1
    cc
    wcel
    @7
    @1
    cN
    eluzelcn
    ax-1cn
    cN
    c1
    npcan
    sylancl
    adantl
    @3
    @4
    @6
    wcel
    @5
    @6
    wcel
    cM
    cN
    eluzp1m1
    cM
    @4
    peano2uz
    syl
    eqeltrrd
end
