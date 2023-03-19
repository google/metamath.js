include "cr.mm"
include "wcel.mm"
include "cc0.mm"
include "cle.mm"
include "wbr.mm"
include "cv.mm"
include "clt.mm"
include "wi.mm"
include "cq.mm"
include "wral.mm"
include "w3a.mm"
include "wceq.mm"
include "wn.mm"
include "wa.mm"
include "wrex.mm"
include "wb.mm"
include "0re.mm"
include "ltnle.mm"
include "mpan.mm"
include "qbtwnre.mm"
include "mp3an1.mm"
include "ex.mm"
include "qre.mm"
include "ltnsym.mm"
include "con2d.mm"
include "sylan2.mm"
include "anim2d.mm"
include "reximdva.mm"
include "syld.mm"
include "sylbird.mm"
include "rexanali.mm"
include "syl6ib.mm"
include "con4d.mm"
include "imp.mm"
include "3adant2.mm"
include "letri3.mm"
include "mpan2.mm"
include "rbaibd.mm"
include "3adant3.mm"
include "mpbird.mm"

theorem qsqueeze
  let vx: setvar x
  let cA: class A

  disjoint A x
  assert |- ( ( A e. RR /\ 0 <_ A /\ A. x e. QQ ( 0 < x -> A < x ) ) -> A = 0 )

  proof
    cA
    cr
    wcel
    #
    cc0
    cA
    cle
    wbr
    #
    cc0
    vx
    cv
    #
    clt
    wbr
    #
    cA
    @2
    clt
    wbr
    #
    wi
    vx
    cq
    wral
    #
    w3a
    cA
    cc0
    wceq
    #
    cA
    cc0
    cle
    wbr
    #
    @0
    @5
    @7
    @1
    @0
    @5
    @7
    @0
    @7
    @5
    @0
    @7
    wn
    #
    @3
    @4
    wn
    #
    wa
    #
    vx
    cq
    wrex
    #
    @5
    wn
    @0
    @8
    cc0
    cA
    clt
    wbr
    #
    @11
    cc0
    cr
    wcel
    #
    @0
    @12
    @8
    wb
    0re
    cc0
    cA
    ltnle
    mpan
    @0
    @12
    @3
    @2
    cA
    clt
    wbr
    #
    wa
    #
    vx
    cq
    wrex
    #
    @11
    @0
    @12
    @16
    @13
    @0
    @12
    @16
    0re
    vx
    cc0
    cA
    qbtwnre
    mp3an1
    ex
    @0
    @15
    @10
    vx
    cq
    @0
    @2
    cq
    wcel
    #
    wa
    @14
    @9
    @3
    @17
    @0
    @2
    cr
    wcel
    #
    @14
    @9
    wi
    @2
    qre
    @0
    @18
    wa
    @4
    @14
    cA
    @2
    ltnsym
    con2d
    sylan2
    anim2d
    reximdva
    syld
    sylbird
    @3
    @4
    vx
    cq
    rexanali
    syl6ib
    con4d
    imp
    3adant2
    @0
    @1
    @6
    @7
    wb
    @5
    @0
    @6
    @7
    @1
    @0
    @13
    @6
    @7
    @1
    wa
    wb
    0re
    cA
    cc0
    letri3
    mpan2
    rbaibd
    3adant3
    mpbird
end
