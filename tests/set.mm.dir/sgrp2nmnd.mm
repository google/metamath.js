include "chash.mm"
include "cfv.mm"
include "c2.mm"
include "wceq.mm"
include "csgrp.mm"
include "wcel.mm"
include "cmnd.mm"
include "wnel.mm"
include "sgrp2nmndlem4.mm"
include "sgrp2nmndlem5.mm"
include "jca.mm"

theorem sgrp2nmnd
  let vx: setvar x
  let vy: setvar y
  let cA: class A
  let cB: class B
  let cS: class S
  let cM: class M
  let va: setvar a
  let vb: setvar b
  let vc: setvar c
  assume mgm2nsgrp.s: |- S = { A , B }
  assume mgm2nsgrp.b: |- ( Base ` M ) = S
  assume sgrp2nmnd.o: |- ( +g ` M ) = ( x e. S , y e. S |-> if ( x = A , A , B ) )

  disjoint S x
  disjoint S y
  disjoint x y
  disjoint A x
  disjoint A y
  disjoint B x
  disjoint B y
  disjoint M x
  disjoint M y
  disjoint M a
  disjoint M b
  disjoint a b
  disjoint S a
  disjoint S b
  disjoint a x
  disjoint a y
  disjoint b x
  disjoint b y
  disjoint A a
  disjoint A b
  disjoint A c
  disjoint a c
  disjoint b c
  disjoint B a
  disjoint B b
  disjoint B c
  disjoint M c
  assert |- ( ( # ` S ) = 2 -> ( M e. SGrp /\ M e/ Mnd ) )

  proof
    cS
    chash
    cfv
    c2
    wceq
    cM
    csgrp
    wcel
    cM
    cmnd
    wnel
    vx
    vy
    cA
    cB
    cS
    cM
    mgm2nsgrp.s
    mgm2nsgrp.b
    sgrp2nmnd.o
    sgrp2nmndlem4
    vx
    vy
    cA
    cB
    cS
    cM
    mgm2nsgrp.s
    mgm2nsgrp.b
    sgrp2nmnd.o
    sgrp2nmndlem5
    jca
end
