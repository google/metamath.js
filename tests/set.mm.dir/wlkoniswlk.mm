include "cwlkson.mm"
include "cfv.mm"
include "co.mm"
include "wbr.mm"
include "cvv.mm"
include "wcel.mm"
include "cvtx.mm"
include "w3a.mm"
include "wa.mm"
include "cwlks.mm"
include "cc0.mm"
include "wceq.mm"
include "chash.mm"
include "eqid.mm"
include "wlkonprop.mm"
include "simp31.mm"
include "syl.mm"

theorem wlkoniswlk
  let cA: class A
  let cB: class B
  let cP: class P
  let cF: class F
  let cG: class G


  assert |- ( F ( A ( WalksOn ` G ) B ) P -> F ( Walks ` G ) P )

  proof
    cF
    cP
    cA
    cB
    cG
    cwlkson
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
    cG
    cwlks
    cfv
    wbr
    #
    cc0
    cP
    cfv
    cA
    wceq
    #
    cF
    chash
    cfv
    cP
    cfv
    cB
    wceq
    #
    w3a
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
    wlkonprop
    @1
    @2
    @3
    @4
    @5
    simp31
    syl
end
