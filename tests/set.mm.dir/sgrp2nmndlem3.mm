include "wcel.mm"
include "wne.mm"
include "w3a.mm"
include "cv.mm"
include "wceq.mm"
include "cif.mm"
include "cmpt2.mm"
include "cplusg.mm"
include "cfv.mm"
include "eqtri.mm"
include "a1i.mm"
include "wa.mm"
include "wn.mm"
include "wi.mm"
include "df-ne.mm"
include "eqcom.mm"
include "wb.mm"
include "eqeq2.mm"
include "adantr.mm"
include "syl5rbbr.mm"
include "notbid.mm"
include "biimpcd.mm"
include "sylbi.mm"
include "3ad2ant3.mm"
include "imp.mm"
include "iffalsed.mm"
include "simp2.mm"
include "simp1.mm"
include "ovmpt2d.mm"

theorem sgrp2nmndlem3
  let vx: setvar x
  let vy: setvar y
  let cA: class A
  let cB: class B
  let cC: class C
  let cS: class S
  let cM: class M
  let c.op: class .o.
  let va: setvar a
  let vb: setvar b
  assume mgm2nsgrp.s: |- S = { A , B }
  assume mgm2nsgrp.b: |- ( Base ` M ) = S
  assume sgrp2nmnd.o: |- ( +g ` M ) = ( x e. S , y e. S |-> if ( x = A , A , B ) )
  assume sgrp2nmnd.p: |- .o. = ( +g ` M )

  disjoint C x
  disjoint C y
  disjoint x y
  disjoint S x
  disjoint S y
  disjoint x y
  disjoint A x
  disjoint A y
  disjoint B x
  disjoint B y
  disjoint M x
  disjoint M a
  disjoint M b
  disjoint a b
  disjoint S a
  disjoint S b
  disjoint a x
  disjoint a y
  disjoint b x
  disjoint b y
  assert |- ( ( C e. S /\ B e. S /\ A =/= B ) -> ( B .o. C ) = B )

  proof
    cC
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
    #
    vx
    vy
    cB
    cC
    cS
    cS
    vx
    cv
    #
    cA
    wceq
    #
    cA
    cB
    cif
    #
    cB
    c.op
    cS
    c.op
    vx
    vy
    cS
    cS
    @6
    cmpt2
    #
    wceq
    @3
    c.op
    cM
    cplusg
    cfv
    @7
    sgrp2nmnd.p
    sgrp2nmnd.o
    eqtri
    a1i
    @3
    @4
    cB
    wceq
    #
    vy
    cv
    cC
    wceq
    #
    wa
    #
    wa
    @5
    cA
    cB
    @3
    @10
    @5
    wn
    #
    @2
    @0
    @10
    @11
    wi
    #
    @1
    @2
    cA
    cB
    wceq
    #
    wn
    #
    @12
    cA
    cB
    df-ne
    @10
    @14
    @11
    @10
    @13
    @5
    @5
    cA
    @4
    wceq
    #
    @10
    @13
    cA
    @4
    eqcom
    @8
    @15
    @13
    wb
    @9
    @4
    cB
    cA
    eqeq2
    adantr
    syl5rbbr
    notbid
    biimpcd
    sylbi
    3ad2ant3
    imp
    iffalsed
    @0
    @1
    @2
    simp2
    #
    @0
    @1
    @2
    simp1
    @16
    ovmpt2d
end
