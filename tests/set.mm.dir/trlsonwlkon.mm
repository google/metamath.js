include "ctrlson.mm"
include "cfv.mm"
include "co.mm"
include "wbr.mm"
include "cvv.mm"
include "wcel.mm"
include "cvtx.mm"
include "w3a.mm"
include "wa.mm"
include "cwlkson.mm"
include "ctrls.mm"
include "eqid.mm"
include "trlsonprop.mm"
include "simp3l.mm"
include "syl.mm"

theorem trlsonwlkon
  let cA: class A
  let cB: class B
  let cP: class P
  let cF: class F
  let cG: class G


  assert |- ( F ( A ( TrailsOn ` G ) B ) P -> F ( A ( WalksOn ` G ) B ) P )

  proof
    cF
    cP
    cA
    cB
    cG
    ctrlson
    cfv
    co
    wbr
    cG
    cvv
    wcel
    cA
    cG
    cvtx
    cfv
    #
    wcel
    cB
    @0
    wcel
    w3a
    #
    cF
    cvv
    wcel
    cP
    cvv
    wcel
    wa
    #
    cF
    cP
    cA
    cB
    cG
    cwlkson
    cfv
    co
    wbr
    #
    cF
    cP
    cG
    ctrls
    cfv
    wbr
    #
    wa
    w3a
    @3
    cA
    cB
    cP
    cF
    cG
    @0
    @0
    eqid
    trlsonprop
    @1
    @2
    @3
    @4
    simp3l
    syl
end
