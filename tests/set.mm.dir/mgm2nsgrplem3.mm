include "wcel.mm"
include "co.mm"
include "wceq.mm"
include "cpr.mm"
include "prid1g.mm"
include "syl6eleqr.mm"
include "prid2g.mm"
include "wa.mm"
include "cv.mm"
include "cif.mm"
include "cmpt2.mm"
include "cplusg.mm"
include "cfv.mm"
include "eqtri.mm"
include "a1i.mm"
include "simprl.mm"
include "simpr.mm"
include "wi.mm"
include "ifeq1.mm"
include "ifid.mm"
include "syl6eq.mm"
include "a1d.mm"
include "wn.mm"
include "eqeq1.mm"
include "biimpcd.mm"
include "adantl.mm"
include "com12.mm"
include "con3d.mm"
include "impcom.mm"
include "iffalsed.mm"
include "ex.mm"
include "pm2.61i.mm"
include "simpl.mm"
include "ovmpt2d.mm"
include "sylan9eqr.mm"
include "jca.mm"
include "iftrued.mm"
include "eqeltrd.mm"
include "syl2an.mm"

theorem mgm2nsgrplem3
  let vx: setvar x
  let vy: setvar y
  let cA: class A
  let cB: class B
  let cS: class S
  let cM: class M
  let cV: class V
  let cW: class W
  let c.op: class .o.
  let va: setvar a
  let vb: setvar b
  assume mgm2nsgrp.s: |- S = { A , B }
  assume mgm2nsgrp.b: |- ( Base ` M ) = S
  assume mgm2nsgrp.o: |- ( +g ` M ) = ( x e. S , y e. S |-> if ( ( x = A /\ y = A ) , B , A ) )
  assume mgm2nsgrp.p: |- .o. = ( +g ` M )

  disjoint .o. x
  disjoint .o. y
  disjoint x y
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
  assert |- ( ( A e. V /\ B e. W ) -> ( A .o. ( A .o. B ) ) = B )

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
    cA
    cA
    cB
    c.op
    co
    #
    c.op
    co
    cB
    wceq
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
    @4
    cB
    @5
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
    #
    vx
    vy
    cA
    @3
    cS
    cS
    vx
    cv
    cA
    wceq
    #
    vy
    cv
    #
    cA
    wceq
    #
    wa
    #
    cB
    cA
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
    @11
    cmpt2
    #
    wceq
    @6
    c.op
    cM
    cplusg
    cfv
    @12
    mgm2nsgrp.p
    mgm2nsgrp.o
    eqtri
    a1i
    #
    @6
    @7
    @8
    @3
    wceq
    #
    wa
    #
    wa
    #
    @10
    cB
    cA
    @16
    @7
    @9
    @6
    @7
    @14
    simprl
    @15
    @6
    @8
    @3
    cA
    @7
    @14
    simpr
    @6
    vx
    vy
    cA
    cB
    cS
    cS
    @11
    cA
    c.op
    cS
    @13
    @7
    @8
    cB
    wceq
    #
    wa
    #
    @11
    cA
    wceq
    #
    @6
    cB
    cA
    wceq
    #
    @18
    @19
    wi
    @20
    @19
    @18
    @20
    @11
    @10
    cA
    cA
    cif
    cA
    @10
    cB
    cA
    cA
    ifeq1
    @10
    cA
    ifid
    syl6eq
    a1d
    @20
    wn
    #
    @18
    @19
    @21
    @18
    wa
    @10
    cB
    cA
    @18
    @21
    @10
    wn
    @18
    @10
    @20
    @17
    @10
    @20
    wi
    @7
    @10
    @17
    @20
    @9
    @17
    @20
    wi
    @7
    @17
    @9
    @20
    @8
    cB
    cA
    eqeq1
    biimpcd
    adantl
    com12
    adantl
    con3d
    impcom
    iffalsed
    ex
    pm2.61i
    adantl
    @1
    @2
    simpl
    #
    @1
    @2
    simpr
    #
    @22
    ovmpt2d
    #
    sylan9eqr
    jca
    iftrued
    @22
    @6
    @3
    cA
    cS
    @24
    @22
    eqeltrd
    @23
    ovmpt2d
    syl2an
end
