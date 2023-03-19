include "csdm.mm"
include "wbr.mm"
include "cdif.mm"
include "c0.mm"
include "wceq.mm"
include "wn.mm"
include "cvv.mm"
include "wcel.mm"
include "wi.mm"
include "relsdom.mm"
include "brrelexi.mm"
include "wss.mm"
include "ssdif0.mm"
include "cdom.mm"
include "ssdomg.mm"
include "domnsym.mm"
include "syl6.mm"
include "syl5bir.mm"
include "syl.mm"
include "con2d.mm"
include "pm2.43i.mm"
include "neqned.mm"

theorem sdomdif
  let cA: class A
  let cB: class B


  assert |- ( A ~< B -> ( B \ A ) =/= (/) )

  proof
    cA
    cB
    csdm
    wbr
    #
    cB
    cA
    cdif
    #
    c0
    @0
    @1
    c0
    wceq
    #
    wn
    @0
    @2
    @0
    @0
    cA
    cvv
    wcel
    #
    @2
    @0
    wn
    #
    wi
    cA
    cB
    csdm
    relsdom
    brrelexi
    @2
    cB
    cA
    wss
    #
    @3
    @4
    cB
    cA
    ssdif0
    @3
    @5
    cB
    cA
    cdom
    wbr
    @4
    cB
    cA
    cvv
    ssdomg
    cB
    cA
    domnsym
    syl6
    syl5bir
    syl
    con2d
    pm2.43i
    neqned
end
