include "cnp.mm"
include "wcel.mm"
include "cv.mm"
include "cltq.mm"
include "wbr.mm"
include "crq.mm"
include "cfv.mm"
include "wn.mm"
include "wa.mm"
include "wex.mm"
include "cab.mm"
include "cmp.mm"
include "co.mm"
include "c1p.mm"
include "wceq.mm"
include "wrex.mm"
include "breq1.mm"
include "anbi1d.mm"
include "exbidv.mm"
include "cbvabv.mm"
include "reclem2pr.mm"
include "reclem4pr.mm"
include "oveq2.mm"
include "eqeq1d.mm"
include "rspcev.mm"
include "syl2anc.mm"

theorem recexpr
  let vx: setvar x
  let cA: class A
  let vy: setvar y
  let vz: setvar z
  let vw: setvar w

  disjoint A x
  disjoint x y
  disjoint x z
  disjoint w x
  disjoint y z
  disjoint w y
  disjoint A y
  disjoint w z
  disjoint A z
  disjoint A w
  assert |- ( A e. P. -> E. x e. P. ( A .P. x ) = 1P )

  proof
    cA
    cnp
    wcel
    vz
    cv
    #
    vy
    cv
    #
    cltq
    wbr
    #
    @1
    crq
    cfv
    cA
    wcel
    wn
    #
    wa
    #
    vy
    wex
    #
    vz
    cab
    #
    cnp
    wcel
    cA
    @6
    cmp
    co
    #
    c1p
    wceq
    #
    cA
    vx
    cv
    #
    cmp
    co
    #
    c1p
    wceq
    #
    vx
    cnp
    wrex
    vw
    vy
    cA
    @6
    @5
    vw
    cv
    #
    @1
    cltq
    wbr
    #
    @3
    wa
    #
    vy
    wex
    vz
    vw
    @0
    @12
    wceq
    #
    @4
    @14
    vy
    @15
    @2
    @13
    @3
    @0
    @12
    @1
    cltq
    breq1
    anbi1d
    exbidv
    cbvabv
    #
    reclem2pr
    vw
    vy
    cA
    @6
    @16
    reclem4pr
    @11
    @8
    vx
    @6
    cnp
    @9
    @6
    wceq
    @10
    @7
    c1p
    @9
    @6
    cA
    cmp
    oveq2
    eqeq1d
    rspcev
    syl2anc
end
