include "cpthson.mm"
include "cfv.mm"
include "co.mm"
include "wbr.mm"
include "cvv.mm"
include "wcel.mm"
include "cvtx.mm"
include "w3a.mm"
include "wa.mm"
include "ctrlson.mm"
include "cpths.mm"
include "eqid.mm"
include "pthsonprop.mm"
include "simp3r.mm"
include "syl.mm"

theorem pthonispth
  let cA: class A
  let cB: class B
  let cP: class P
  let cF: class F
  let cG: class G


  assert |- ( F ( A ( PathsOn ` G ) B ) P -> F ( Paths ` G ) P )

  proof
    cF
    cP
    cA
    cB
    cG
    cpthson
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
    cpths
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
    pthsonprop
    @1
    @2
    @3
    @4
    simp3r
    syl
end
