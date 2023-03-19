include "csn.mm"
include "wdisj.mm"
include "cv.mm"
include "wcel.mm"
include "wa.mm"
include "wmo.mm"
include "dfdisj2.mm"
include "wceq.mm"
include "moeq.mm"
include "elsni.mm"
include "adantr.mm"
include "moimi.mm"
include "ax-mp.mm"
include "mpgbir.mm"

theorem disjxsn
  let vx: setvar x
  let cA: class A
  let cB: class B
  let vy: setvar y

  disjoint A x
  disjoint x y
  disjoint A y
  disjoint B y
  assert |- Disj_ x e. { A } B

  proof
    vx
    cA
    csn
    #
    cB
    wdisj
    vx
    cv
    #
    @0
    wcel
    #
    vy
    cv
    cB
    wcel
    #
    wa
    #
    vx
    wmo
    #
    vy
    vx
    vy
    @0
    cB
    dfdisj2
    @1
    cA
    wceq
    #
    vx
    wmo
    @5
    vx
    cA
    moeq
    @4
    @6
    vx
    @2
    @6
    @3
    @1
    cA
    elsni
    adantr
    moimi
    ax-mp
    mpgbir
end
