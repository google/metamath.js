include "cz.mm"
include "wcel.mm"
include "c1.mm"
include "caddc.mm"
include "co.mm"
include "cuz.mm"
include "cfv.mm"
include "wa.mm"
include "cmin.mm"
include "cseq.mm"
include "wceq.mm"
include "eluzp1m1.mm"
include "seqp1.mm"
include "syl.mm"
include "cc.mm"
include "eluzelcn.mm"
include "ax-1cn.mm"
include "npcan.mm"
include "sylancl.mm"
include "adantl.mm"
include "fveq2d.mm"
include "oveq2d.mm"
include "3eqtr3d.mm"

theorem seqm1
  let c.pl: class .+
  let cF: class F
  let cM: class M
  let cN: class N


  assert |- ( ( M e. ZZ /\ N e. ( ZZ>= ` ( M + 1 ) ) ) -> ( seq M ( .+ , F ) ` N ) = ( ( seq M ( .+ , F ) ` ( N - 1 ) ) .+ ( F ` N ) ) )

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
    c.pl
    cF
    cM
    cseq
    #
    cfv
    #
    @4
    @6
    cfv
    #
    @5
    cF
    cfv
    #
    c.pl
    co
    #
    cN
    @6
    cfv
    @8
    cN
    cF
    cfv
    #
    c.pl
    co
    @3
    @4
    cM
    cuz
    cfv
    wcel
    @7
    @10
    wceq
    cM
    cN
    eluzp1m1
    c.pl
    cF
    cM
    @4
    seqp1
    syl
    @3
    @5
    cN
    @6
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
    @12
    @1
    cN
    eluzelcn
    ax-1cn
    cN
    c1
    npcan
    sylancl
    adantl
    #
    fveq2d
    @3
    @9
    @11
    @8
    c.pl
    @3
    @5
    cN
    cF
    @13
    fveq2d
    oveq2d
    3eqtr3d
end
