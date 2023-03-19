include "cr.mm"
include "wss.mm"
include "cfn.mm"
include "wcel.mm"
include "wa.mm"
include "c0.mm"
include "wceq.mm"
include "cv.mm"
include "cle.mm"
include "wbr.mm"
include "wral.mm"
include "wrex.mm"
include "cc0.mm"
include "0red.mm"
include "rzal.mm"
include "breq1.mm"
include "ralbidv.mm"
include "rspcev.mm"
include "syl2anc.mm"
include "adantl.mm"
include "wn.mm"
include "wne.mm"
include "neqne.mm"
include "simpll.mm"
include "simplr.mm"
include "simpr.mm"
include "fiminre.mm"
include "syl3anc.mm"
include "ssrexv.mm"
include "sylc.mm"
include "syldan.mm"
include "pm2.61dan.mm"

theorem fiminre2
  let vx: setvar x
  let vy: setvar y
  let cA: class A

  disjoint A x
  disjoint A y
  disjoint x y
  assert |- ( ( A C_ RR /\ A e. Fin ) -> E. x e. RR A. y e. A x <_ y )

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
    cA
    c0
    wceq
    #
    vx
    cv
    #
    vy
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
    @3
    @8
    @2
    @3
    cc0
    cr
    wcel
    cc0
    @5
    cle
    wbr
    #
    vy
    cA
    wral
    #
    @8
    @3
    0red
    @9
    vy
    cA
    rzal
    @7
    @10
    vx
    cc0
    cr
    @4
    cc0
    wceq
    @6
    @9
    vy
    cA
    @4
    cc0
    @5
    cle
    breq1
    ralbidv
    rspcev
    syl2anc
    adantl
    @2
    @3
    wn
    #
    cA
    c0
    wne
    #
    @8
    @11
    @12
    @2
    cA
    c0
    neqne
    adantl
    @2
    @12
    wa
    #
    @0
    @7
    vx
    cA
    wrex
    #
    @8
    @0
    @1
    @12
    simpll
    #
    @13
    @0
    @1
    @12
    @14
    @15
    @0
    @1
    @12
    simplr
    @2
    @12
    simpr
    vx
    vy
    cA
    fiminre
    syl3anc
    @7
    vx
    cA
    cr
    ssrexv
    sylc
    syldan
    pm2.61dan
end
