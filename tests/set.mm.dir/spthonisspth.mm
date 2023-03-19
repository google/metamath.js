include "cspthson.mm"
include "cfv.mm"
include "co.mm"
include "wbr.mm"
include "cvv.mm"
include "wcel.mm"
include "cvtx.mm"
include "w3a.mm"
include "wa.mm"
include "ctrlson.mm"
include "cspths.mm"
include "eqid.mm"
include "spthonprop.mm"
include "simp3r.mm"
include "syl.mm"

theorem spthonisspth
  let cA: class A
  let cB: class B
  let cP: class P
  let cF: class F
  let cG: class G


  assert |- ( F ( A ( SPathsOn ` G ) B ) P -> F ( SPaths ` G ) P )

  proof
    cF
    cP
    cA
    cB
    cG
    cspthson
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
    ctrlson
    cfv
    co
    wbr
    #
    cF
    cP
    cG
    cspths
    cfv
    wbr
    #
    wa
    w3a
    @4
    cA
    cB
    cP
    cF
    cG
    @0
    @0
    eqid
    spthonprop
    @1
    @2
    @3
    @4
    simp3r
    syl
end
