include "wne.mm"
include "cvv.mm"
include "wcel.mm"
include "csn.mm"
include "wn.mm"
include "wa.mm"
include "wceq.mm"
include "neneq.mm"
include "adantr.mm"
include "wb.mm"
include "elsng.mm"
include "adantl.mm"
include "mtbird.mm"
include "prcnel.mm"
include "pm2.61dan.mm"

theorem nelsnOLD
  let cA: class A
  let cB: class B


  assert |- ( A =/= B -> -. A e. { B } )

  proof
    cA
    cB
    wne
    #
    cA
    cvv
    wcel
    #
    cA
    cB
    csn
    #
    wcel
    #
    wn
    #
    @0
    @1
    wa
    @3
    cA
    cB
    wceq
    #
    @0
    @5
    wn
    @1
    cA
    cB
    neneq
    adantr
    @1
    @3
    @5
    wb
    @0
    cA
    cB
    cvv
    elsng
    adantl
    mtbird
    @1
    wn
    @4
    @0
    cA
    @2
    prcnel
    adantl
    pm2.61dan
end
