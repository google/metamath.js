include "wcel.mm"
include "cmgm.mm"
include "cpr.mm"
include "prid1g.mm"
include "syl6eleqr.mm"
include "prid2g.mm"
include "wa.mm"
include "cv.mm"
include "wceq.mm"
include "cbs.mm"
include "cfv.mm"
include "eqcomi.mm"
include "c0.mm"
include "wne.mm"
include "ne0i.mm"
include "adantr.mm"
include "simplr.mm"
include "simpll.mm"
include "opifismgm.mm"
include "syl2an.mm"

theorem mgm2nsgrplem1
  let vx: setvar x
  let vy: setvar y
  let cA: class A
  let cB: class B
  let cS: class S
  let cM: class M
  let cV: class V
  let cW: class W
  let va: setvar a
  let vb: setvar b
  assume mgm2nsgrp.s: |- S = { A , B }
  assume mgm2nsgrp.b: |- ( Base ` M ) = S
  assume mgm2nsgrp.o: |- ( +g ` M ) = ( x e. S , y e. S |-> if ( ( x = A /\ y = A ) , B , A ) )

  disjoint A x
  disjoint A y
  disjoint x y
  disjoint B x
  disjoint B y
  disjoint M x
  disjoint S x
  disjoint S y
  disjoint x y
  disjoint M a
  disjoint M b
  disjoint a b
  disjoint S a
  disjoint S b
  disjoint a x
  disjoint a y
  disjoint b x
  disjoint b y
  assert |- ( ( A e. V /\ B e. W ) -> M e. Mgm )

  proof
    cA
    cV
    wcel
    #
    cA
    cS
    wcel
    #
    cB
    cS
    wcel
    #
    cM
    cmgm
    wcel
    cB
    cW
    wcel
    #
    @0
    cA
    cA
    cB
    cpr
    #
    cS
    cA
    cB
    cV
    prid1g
    mgm2nsgrp.s
    syl6eleqr
    @3
    cB
    @4
    cS
    cA
    cB
    cW
    prid2g
    mgm2nsgrp.s
    syl6eleqr
    @1
    @2
    wa
    vx
    cv
    #
    cA
    wceq
    vy
    cv
    #
    cA
    wceq
    wa
    vx
    vy
    cS
    cB
    cA
    cM
    cM
    cbs
    cfv
    cS
    mgm2nsgrp.b
    eqcomi
    mgm2nsgrp.o
    @1
    cS
    c0
    wne
    @2
    cS
    cA
    ne0i
    adantr
    @1
    @2
    @5
    cS
    wcel
    @6
    cS
    wcel
    wa
    #
    simplr
    @1
    @2
    @7
    simpll
    opifismgm
    syl2an
end
