include "chash.mm"
include "cfv.mm"
include "c2.mm"
include "wceq.mm"
include "cmgm.mm"
include "wcel.mm"
include "csgrp.mm"
include "wnel.mm"
include "wne.mm"
include "w3a.mm"
include "hashprdifel.mm"
include "mgm2nsgrplem1.mm"
include "3adant3.mm"
include "syl.mm"
include "mgm2nsgrplem4.mm"
include "jca.mm"

theorem mgm2nsgrp
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
  assert |- ( ( # ` S ) = 2 -> ( M e. Mgm /\ M e/ SGrp ) )

  proof
    cS
    chash
    cfv
    c2
    wceq
    #
    cM
    cmgm
    wcel
    #
    cM
    csgrp
    wnel
    @0
    cA
    cS
    wcel
    #
    cB
    cS
    wcel
    #
    cA
    cB
    wne
    #
    w3a
    @1
    cA
    cB
    cS
    mgm2nsgrp.s
    hashprdifel
    @2
    @3
    @1
    @4
    vx
    vy
    cA
    cB
    cS
    cM
    cS
    cS
    mgm2nsgrp.s
    mgm2nsgrp.b
    mgm2nsgrp.o
    mgm2nsgrplem1
    3adant3
    syl
    vx
    vy
    cA
    cB
    cS
    cM
    mgm2nsgrp.s
    mgm2nsgrp.b
    mgm2nsgrp.o
    mgm2nsgrplem4
    jca
end
