include "cn.mm"
include "csquarenn.mm"
include "cdif.mm"
include "wcel.mm"
include "c1.mm"
include "cpellfund.mm"
include "cfv.mm"
include "1red.mm"
include "pellfundgt1.mm"
include "gtned.mm"

theorem pellfundne1
  let cD: class D
  let va: setvar a
  let vb: setvar b
  let vc: setvar c
  let vd: setvar d
  let cA: class A
  let vx: setvar x


  assert |- ( D e. ( NN \ []NN ) -> ( PellFund ` D ) =/= 1 )

  proof
    cD
    cn
    csquarenn
    cdif
    wcel
    #
    c1
    cD
    cpellfund
    cfv
    @0
    1red
    cD
    pellfundgt1
    gtned
end
