include "cr.mm"
include "wss.mm"
include "cfn.mm"
include "wcel.mm"
include "wa.mm"
include "cv.mm"
include "cle.mm"
include "wbr.mm"
include "wral.mm"
include "wrex.mm"
include "c0.mm"
include "wceq.mm"
include "wi.mm"
include "cc0.mm"
include "0re.mm"
include "rzal.mm"
include "breq2.mm"
include "ralbidv.mm"
include "rspcev.mm"
include "sylancr.mm"
include "a1i.mm"
include "wne.mm"
include "fimaxre.mm"
include "3expia.mm"
include "ssrexv.mm"
include "adantr.mm"
include "syld.mm"
include "pm2.61dne.mm"

theorem fimaxre2
  let vx: setvar x
  let vy: setvar y
  let cA: class A

  disjoint A x
  disjoint A y
  disjoint x y
  assert |- ( ( A C_ RR /\ A e. Fin ) -> E. x e. RR A. y e. A y <_ x )

  proof
    cA
    cr
    wss
    #
    cA
    cfn
    wcel
    #
    wa
    #
    vy
    cv
    #
    vx
    cv
    #
    cle
    wbr
    #
    vy
    cA
    wral
    #
    vx
    cr
    wrex
    #
    cA
    c0
    cA
    c0
    wceq
    #
    @7
    wi
    @2
    @8
    cc0
    cr
    wcel
    @3
    cc0
    cle
    wbr
    #
    vy
    cA
    wral
    #
    @7
    0re
    @9
    vy
    cA
    rzal
    @6
    @10
    vx
    cc0
    cr
    @4
    cc0
    wceq
    @5
    @9
    vy
    cA
    @4
    cc0
    @3
    cle
    breq2
    ralbidv
    rspcev
    sylancr
    a1i
    @2
    cA
    c0
    wne
    #
    @6
    vx
    cA
    wrex
    #
    @7
    @0
    @1
    @11
    @12
    vx
    vy
    cA
    fimaxre
    3expia
    @0
    @12
    @7
    wi
    @1
    @6
    vx
    cA
    cr
    ssrexv
    adantr
    syld
    pm2.61dne
end
