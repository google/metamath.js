include "cfzo.mm"
include "co.mm"
include "cin.mm"
include "c0.mm"
include "wceq.mm"
include "cv.mm"
include "wcel.mm"
include "wn.mm"
include "wi.mm"
include "disj1.mm"
include "cle.mm"
include "wbr.mm"
include "clt.mm"
include "elfzolt2.mm"
include "elfzoelz.mm"
include "zred.mm"
include "elfzoel2.mm"
include "ltnled.mm"
include "mpbid.mm"
include "elfzole1.mm"
include "nsyl.mm"
include "mpgbir.mm"

theorem fzodisj
  let cA: class A
  let cB: class B
  let cC: class C
  let vx: setvar x
  let cD: class D


  assert |- ( ( A ..^ B ) i^i ( B ..^ C ) ) = (/)

  proof
    cA
    cB
    cfzo
    co
    #
    cB
    cC
    cfzo
    co
    #
    cin
    c0
    wceq
    vx
    cv
    #
    @0
    wcel
    #
    @2
    @1
    wcel
    #
    wn
    wi
    vx
    vx
    @0
    @1
    disj1
    @3
    cB
    @2
    cle
    wbr
    #
    @4
    @3
    @2
    cB
    clt
    wbr
    @5
    wn
    @2
    cA
    cB
    elfzolt2
    @3
    @2
    cB
    @3
    @2
    @2
    cA
    cB
    elfzoelz
    zred
    @3
    cB
    @2
    cA
    cB
    elfzoel2
    zred
    ltnled
    mpbid
    @2
    cB
    cC
    elfzole1
    nsyl
    mpgbir
end
