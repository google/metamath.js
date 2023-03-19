include "cr.mm"
include "wss.mm"
include "c0.mm"
include "wne.mm"
include "cv.mm"
include "cle.mm"
include "wbr.mm"
include "wral.mm"
include "wrex.mm"
include "w3a.mm"
include "wcel.mm"
include "wa.mm"
include "clt.mm"
include "csup.mm"
include "wn.mm"
include "suprlub.mm"
include "notbid.mm"
include "ralnex.mm"
include "syl6bbr.mm"

theorem suprnub
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let cA: class A
  let cB: class B
  let vw: setvar w

  disjoint A x
  disjoint A y
  disjoint x y
  disjoint A z
  disjoint B z
  disjoint A w
  disjoint w x
  disjoint w y
  disjoint w z
  disjoint B w
  assert |- ( ( ( A C_ RR /\ A =/= (/) /\ E. x e. RR A. y e. A y <_ x ) /\ B e. RR ) -> ( -. B < sup ( A , RR , < ) <-> A. z e. A -. B < z ) )

  proof
    cA
    cr
    wss
    cA
    c0
    wne
    vy
    cv
    vx
    cv
    cle
    wbr
    vy
    cA
    wral
    vx
    cr
    wrex
    w3a
    cB
    cr
    wcel
    wa
    #
    cB
    cA
    cr
    clt
    csup
    clt
    wbr
    #
    wn
    cB
    vz
    cv
    clt
    wbr
    #
    vz
    cA
    wrex
    #
    wn
    @2
    wn
    vz
    cA
    wral
    @0
    @1
    @3
    vx
    vy
    vz
    cA
    cB
    suprlub
    notbid
    @2
    vz
    cA
    ralnex
    syl6bbr
end
