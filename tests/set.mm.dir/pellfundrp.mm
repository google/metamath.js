include "cn.mm"
include "csquarenn.mm"
include "cdif.mm"
include "wcel.mm"
include "cpellfund.mm"
include "cfv.mm"
include "pellfundre.mm"
include "cc0.mm"
include "c1.mm"
include "0red.mm"
include "1red.mm"
include "clt.mm"
include "wbr.mm"
include "0lt1.mm"
include "a1i.mm"
include "pellfundgt1.mm"
include "lttrd.mm"
include "elrpd.mm"

theorem pellfundrp
  let cD: class D
  let va: setvar a
  let vb: setvar b
  let vc: setvar c
  let vd: setvar d
  let cA: class A
  let vx: setvar x


  assert |- ( D e. ( NN \ []NN ) -> ( PellFund ` D ) e. RR+ )

  proof
    cD
    cn
    csquarenn
    cdif
    wcel
    #
    cD
    cpellfund
    cfv
    #
    cD
    pellfundre
    #
    @0
    cc0
    c1
    @1
    @0
    0red
    @0
    1red
    @2
    cc0
    c1
    clt
    wbr
    @0
    0lt1
    a1i
    cD
    pellfundgt1
    lttrd
    elrpd
end
