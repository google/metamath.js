include "crp.mm"
include "wcel.mm"
include "c1.mm"
include "cle.mm"
include "wbr.mm"
include "wa.mm"
include "cv.mm"
include "c2.mm"
include "cexp.mm"
include "co.mm"
include "crab.mm"
include "cr.mm"
include "clt.mm"
include "csup.mm"
include "wceq.mm"
include "wrex.mm"
include "eqid.mm"
include "sqrlem4.mm"
include "cmul.mm"
include "cab.mm"
include "sqrlem7.mm"
include "breq1.mm"
include "oveq1.mm"
include "eqeq1d.mm"
include "anbi12d.mm"
include "rspcev.mm"
include "anassrs.mm"
include "syl2anc.mm"

theorem 01sqrex
  let vx: setvar x
  let cA: class A
  let vw: setvar w
  let vy: setvar y
  let vz: setvar z

  disjoint A x
  disjoint A w
  disjoint A y
  disjoint A z
  disjoint w x
  disjoint w y
  disjoint w z
  disjoint x y
  disjoint x z
  disjoint y z
  assert |- ( ( A e. RR+ /\ A <_ 1 ) -> E. x e. RR+ ( x <_ 1 /\ ( x ^ 2 ) = A ) )

  proof
    cA
    crp
    wcel
    cA
    c1
    cle
    wbr
    wa
    vy
    cv
    c2
    cexp
    co
    cA
    cle
    wbr
    vy
    crp
    crab
    #
    cr
    clt
    csup
    #
    crp
    wcel
    #
    @1
    c1
    cle
    wbr
    #
    wa
    @1
    c2
    cexp
    co
    #
    cA
    wceq
    #
    vx
    cv
    #
    c1
    cle
    wbr
    #
    @6
    c2
    cexp
    co
    #
    cA
    wceq
    #
    wa
    #
    vx
    crp
    wrex
    #
    vy
    cA
    @1
    @0
    @0
    eqid
    #
    @1
    eqid
    #
    sqrlem4
    vy
    vz
    cA
    @1
    @0
    vz
    cv
    vw
    cv
    @6
    cmul
    co
    wceq
    vx
    @0
    wrex
    vw
    @0
    wrex
    vz
    cab
    #
    vw
    vx
    @12
    @13
    @14
    eqid
    sqrlem7
    @2
    @3
    @5
    @11
    @10
    @3
    @5
    wa
    vx
    @1
    crp
    @6
    @1
    wceq
    #
    @7
    @3
    @9
    @5
    @6
    @1
    c1
    cle
    breq1
    @15
    @8
    @4
    cA
    @6
    @1
    c2
    cexp
    oveq1
    eqeq1d
    anbi12d
    rspcev
    anassrs
    syl2anc
end
