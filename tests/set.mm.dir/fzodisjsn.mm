include "cfzo.mm"
include "co.mm"
include "csn.mm"
include "cin.mm"
include "c0.mm"
include "wceq.mm"
include "cv.mm"
include "wcel.mm"
include "wn.mm"
include "wi.mm"
include "disj1.mm"
include "elfzoelz.mm"
include "zred.mm"
include "elfzolt2.mm"
include "ltned.mm"
include "neneqd.mm"
include "elsni.mm"
include "nsyl.mm"
include "mpgbir.mm"

theorem fzodisjsn
  let cA: class A
  let cB: class B
  let vx: setvar x


  assert |- ( ( A ..^ B ) i^i { B } ) = (/)

  proof
    cA
    cB
    cfzo
    co
    #
    cB
    csn
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
    @2
    cB
    wceq
    @4
    @3
    @2
    cB
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
    @2
    cA
    cB
    elfzolt2
    ltned
    neneqd
    @2
    cB
    elsni
    nsyl
    mpgbir
end
