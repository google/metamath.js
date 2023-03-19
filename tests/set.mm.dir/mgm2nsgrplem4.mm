include "chash.mm"
include "cfv.mm"
include "c2.mm"
include "wceq.mm"
include "wcel.mm"
include "w3a.mm"
include "cplusg.mm"
include "co.mm"
include "wne.mm"
include "csgrp.mm"
include "wnel.mm"
include "hashprdifel.mm"
include "simp1.mm"
include "simp2.mm"
include "3jca.mm"
include "syl.mm"
include "simp3.mm"
include "eqid.mm"
include "mgm2nsgrplem2.mm"
include "3adant3.mm"
include "mgm2nsgrplem3.mm"
include "3netr4d.mm"
include "cbs.mm"
include "eqcomi.mm"
include "isnsgrp.mm"
include "sylc.mm"

theorem mgm2nsgrplem4
  let vx: setvar x
  let vy: setvar y
  let cA: class A
  let cB: class B
  let cS: class S
  let cM: class M
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
  disjoint M y
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
  assert |- ( ( # ` S ) = 2 -> M e/ SGrp )

  proof
    cS
    chash
    cfv
    c2
    wceq
    #
    cA
    cS
    wcel
    #
    @1
    cB
    cS
    wcel
    #
    w3a
    #
    cA
    cA
    cM
    cplusg
    cfv
    #
    co
    cB
    @4
    co
    #
    cA
    cA
    cB
    @4
    co
    @4
    co
    #
    wne
    #
    cM
    csgrp
    wnel
    @0
    @1
    @2
    cA
    cB
    wne
    #
    w3a
    #
    @3
    cA
    cB
    cS
    mgm2nsgrp.s
    hashprdifel
    #
    @9
    @1
    @1
    @2
    @1
    @2
    @8
    simp1
    #
    @11
    @1
    @2
    @8
    simp2
    3jca
    syl
    @0
    @9
    @7
    @10
    @9
    cA
    cB
    @5
    @6
    @1
    @2
    @8
    simp3
    @1
    @2
    @5
    cA
    wceq
    @8
    vx
    vy
    cA
    cB
    cS
    cM
    cS
    cS
    @4
    mgm2nsgrp.s
    mgm2nsgrp.b
    mgm2nsgrp.o
    @4
    eqid
    #
    mgm2nsgrplem2
    3adant3
    @1
    @2
    @6
    cB
    wceq
    @8
    vx
    vy
    cA
    cB
    cS
    cM
    cS
    cS
    @4
    mgm2nsgrp.s
    mgm2nsgrp.b
    mgm2nsgrp.o
    @12
    mgm2nsgrplem3
    3adant3
    3netr4d
    syl
    cS
    cM
    cA
    cA
    @4
    cB
    cM
    cbs
    cfv
    cS
    mgm2nsgrp.b
    eqcomi
    @12
    isnsgrp
    sylc
end
