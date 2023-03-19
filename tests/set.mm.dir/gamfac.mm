include "cn.mm"
include "wcel.mm"
include "c1.mm"
include "cmin.mm"
include "co.mm"
include "cfa.mm"
include "cfv.mm"
include "caddc.mm"
include "cgam.mm"
include "cn0.mm"
include "wceq.mm"
include "nnm1nn0.mm"
include "facgam.mm"
include "syl.mm"
include "nncn.mm"
include "1cnd.mm"
include "npcand.mm"
include "fveq2d.mm"
include "eqtr2d.mm"

theorem gamfac
  let cN: class N
  let vn: setvar n
  let vx: setvar x


  assert |- ( N e. NN -> ( _G ` N ) = ( ! ` ( N - 1 ) ) )

  proof
    cN
    cn
    wcel
    #
    cN
    c1
    cmin
    co
    #
    cfa
    cfv
    #
    @1
    c1
    caddc
    co
    #
    cgam
    cfv
    #
    cN
    cgam
    cfv
    @0
    @1
    cn0
    wcel
    @2
    @4
    wceq
    cN
    nnm1nn0
    @1
    facgam
    syl
    @0
    @3
    cN
    cgam
    @0
    cN
    c1
    cN
    nncn
    @0
    1cnd
    npcand
    fveq2d
    eqtr2d
end
