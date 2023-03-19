include "cz.mm"
include "wcel.mm"
include "c1.mm"
include "caddc.mm"
include "co.mm"
include "cfzo.mm"
include "cmin.mm"
include "cfz.mm"
include "wceq.mm"
include "peano2z.mm"
include "fzoval.mm"
include "syl.mm"
include "cc.mm"
include "zcn.mm"
include "ax-1cn.mm"
include "pncan.mm"
include "sylancl.mm"
include "oveq2d.mm"
include "eqtr2d.mm"

theorem fzval3
  let cM: class M
  let cN: class N


  assert |- ( N e. ZZ -> ( M ... N ) = ( M ..^ ( N + 1 ) ) )

  proof
    cN
    cz
    wcel
    #
    cM
    cN
    c1
    caddc
    co
    #
    cfzo
    co
    #
    cM
    @1
    c1
    cmin
    co
    #
    cfz
    co
    #
    cM
    cN
    cfz
    co
    @0
    @1
    cz
    wcel
    @2
    @4
    wceq
    cN
    peano2z
    cM
    @1
    fzoval
    syl
    @0
    @3
    cN
    cM
    cfz
    @0
    cN
    cc
    wcel
    c1
    cc
    wcel
    @3
    cN
    wceq
    cN
    zcn
    ax-1cn
    cN
    c1
    pncan
    sylancl
    oveq2d
    eqtr2d
end
