include "cc0.mm"
include "cr.mm"
include "wcel.mm"
include "cv.mm"
include "cle.mm"
include "wbr.mm"
include "crp.mm"
include "cin.mm"
include "wral.mm"
include "wrex.mm"
include "0re.mm"
include "inss1.mm"
include "sseli.mm"
include "rpge0d.mm"
include "rgen.mm"
include "wceq.mm"
include "breq1.mm"
include "ralbidv.mm"
include "rspcev.mm"
include "mp2an.mm"

theorem taupilemrplb
  let vx: setvar x
  let vy: setvar y
  let cA: class A

  disjoint x y
  disjoint A x
  assert |- E. x e. RR A. y e. ( RR+ i^i A ) x <_ y

  proof
    cc0
    cr
    wcel
    cc0
    vy
    cv
    #
    cle
    wbr
    #
    vy
    crp
    cA
    cin
    #
    wral
    #
    vx
    cv
    #
    @0
    cle
    wbr
    #
    vy
    @2
    wral
    #
    vx
    cr
    wrex
    0re
    @1
    vy
    @2
    @0
    @2
    wcel
    @0
    @2
    crp
    @0
    crp
    cA
    inss1
    sseli
    rpge0d
    rgen
    @6
    @3
    vx
    cc0
    cr
    @4
    cc0
    wceq
    @5
    @1
    vy
    @2
    @4
    cc0
    @0
    cle
    breq1
    ralbidv
    rspcev
    mp2an
end
