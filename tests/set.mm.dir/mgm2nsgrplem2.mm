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
include "wi.mm"
include "ifeq1.mm"
include "ifid.mm"
include "syl6eq.mm"
include "a1d.mm"
include "wn.mm"
include "eqeq1.mm"
include "bicomd.mm"
include "notbid.mm"
include "biimpac.mm"
include "intnand.mm"
include "iffalsed.mm"
include "ex.mm"
include "pm2.61i.mm"
include "ad2antll.mm"
include "iftrue.mm"
include "adantl.mm"
include "simpl.mm"
include "simpr.mm"
include "ovmpt2d.mm"
include "eqeltrd.mm"
include "syl2an.mm"

theorem mgm2nsgrplem2
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
  assert |- ( ( A e. V /\ B e. W ) -> ( ( A .o. A ) .o. B ) = A )

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
    c.op
    co
    #
    cB
    c.op
    co
    cA
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
    @3
    cB
    cS
    cS
    vx
    cv
    #
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
    cA
    c.op
    cS
    c.op
    vx
    vy
    cS
    cS
    @12
    cmpt2
    #
    wceq
    @6
    c.op
    cM
    cplusg
    cfv
    @13
    mgm2nsgrp.p
    mgm2nsgrp.o
    eqtri
    a1i
    #
    @9
    cB
    wceq
    #
    @12
    cA
    wceq
    #
    @6
    @7
    @3
    wceq
    cB
    cA
    wceq
    #
    @15
    @16
    wi
    @17
    @16
    @15
    @17
    @12
    @11
    cA
    cA
    cif
    cA
    @11
    cB
    cA
    cA
    ifeq1
    @11
    cA
    ifid
    syl6eq
    a1d
    @17
    wn
    #
    @15
    @16
    @18
    @15
    wa
    #
    @11
    cB
    cA
    @19
    @10
    @8
    @15
    @18
    @10
    wn
    @15
    @17
    @10
    @15
    @10
    @17
    @9
    cB
    cA
    eqeq1
    bicomd
    notbid
    biimpac
    intnand
    iffalsed
    ex
    pm2.61i
    ad2antll
    @6
    @3
    cB
    cS
    @6
    vx
    vy
    cA
    cA
    cS
    cS
    @12
    cB
    c.op
    cS
    @14
    @11
    @12
    cB
    wceq
    @6
    @11
    cB
    cA
    iftrue
    adantl
    @1
    @2
    simpl
    #
    @20
    @1
    @2
    simpr
    #
    ovmpt2d
    @21
    eqeltrd
    @21
    @20
    ovmpt2d
    syl2an
end
