include "wcel.mm"
include "wa.mm"
include "cv.mm"
include "co.mm"
include "wceq.mm"
include "wral.mm"
include "cpr.mm"
include "prid1g.mm"
include "syl6eleqr.mm"
include "prid2g.mm"
include "simpl.mm"
include "sgrp2nmndlem2.mm"
include "syldan.mm"
include "wi.mm"
include "oveq1.mm"
include "id.mm"
include "eqeq12d.mm"
include "syl5ib.mm"
include "wn.mm"
include "wne.mm"
include "simprl.mm"
include "simprr.mm"
include "df-ne.mm"
include "biimpri.mm"
include "adantr.mm"
include "sgrp2nmndlem3.mm"
include "syl3anc.mm"
include "ex.mm"
include "pm2.61i.mm"
include "oveq12d.mm"
include "jca.mm"
include "jca31.mm"
include "syl2an.mm"
include "raleqi.mm"
include "ralprg.mm"
include "syl5bb.mm"
include "ralbidv.mm"
include "oveq2.mm"
include "eqeq1d.mm"
include "anbi12d.mm"
include "bitrd.mm"
include "mpbird.mm"

theorem sgrp2rid2
  let vx: setvar x
  let vy: setvar y
  let cA: class A
  let cB: class B
  let cS: class S
  let cM: class M
  let cV: class V
  let cW: class W
  let c.op: class .o.
  let cC: class C
  let va: setvar a
  let vb: setvar b
  assume mgm2nsgrp.s: |- S = { A , B }
  assume mgm2nsgrp.b: |- ( Base ` M ) = S
  assume sgrp2nmnd.o: |- ( +g ` M ) = ( x e. S , y e. S |-> if ( x = A , A , B ) )
  assume sgrp2nmnd.p: |- .o. = ( +g ` M )

  disjoint x y
  disjoint V x
  disjoint W x
  disjoint .o. x
  disjoint .o. y
  disjoint S x
  disjoint S y
  disjoint x y
  disjoint A x
  disjoint A y
  disjoint B x
  disjoint B y
  disjoint M x
  disjoint C x
  disjoint C y
  disjoint M a
  disjoint M b
  disjoint a b
  disjoint S a
  disjoint S b
  disjoint a x
  disjoint a y
  disjoint b x
  disjoint b y
  assert |- ( ( A e. V /\ B e. W ) -> A. x e. S A. y e. S ( y .o. x ) = y )

  proof
    cA
    cV
    wcel
    #
    cB
    cW
    wcel
    #
    wa
    #
    vy
    cv
    #
    vx
    cv
    #
    c.op
    co
    #
    @3
    wceq
    #
    vy
    cS
    wral
    #
    vx
    cS
    wral
    #
    cA
    cA
    c.op
    co
    #
    cA
    wceq
    #
    cB
    cA
    c.op
    co
    #
    cB
    wceq
    #
    wa
    #
    cA
    cB
    c.op
    co
    #
    cA
    wceq
    #
    cB
    cB
    c.op
    co
    #
    cB
    wceq
    #
    wa
    #
    wa
    #
    @0
    cA
    cS
    wcel
    #
    cB
    cS
    wcel
    #
    @19
    @1
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
    @1
    cB
    @22
    cS
    cA
    cB
    cW
    prid2g
    mgm2nsgrp.s
    syl6eleqr
    @20
    @21
    wa
    #
    @10
    @12
    @18
    @20
    @21
    @20
    @10
    @20
    @21
    simpl
    vx
    vy
    cA
    cB
    cA
    cS
    cM
    c.op
    mgm2nsgrp.s
    mgm2nsgrp.b
    sgrp2nmnd.o
    sgrp2nmnd.p
    sgrp2nmndlem2
    syldan
    #
    cA
    cB
    wceq
    #
    @23
    @12
    wi
    @23
    @10
    @25
    @12
    @24
    @25
    @9
    @11
    cA
    cB
    cA
    cB
    cA
    c.op
    oveq1
    @25
    id
    #
    eqeq12d
    syl5ib
    @25
    wn
    #
    @23
    @12
    @27
    @23
    wa
    #
    @20
    @21
    cA
    cB
    wne
    #
    @12
    @27
    @20
    @21
    simprl
    @27
    @20
    @21
    simprr
    #
    @27
    @29
    @23
    @29
    @27
    cA
    cB
    df-ne
    biimpri
    adantr
    #
    vx
    vy
    cA
    cB
    cA
    cS
    cM
    c.op
    mgm2nsgrp.s
    mgm2nsgrp.b
    sgrp2nmnd.o
    sgrp2nmnd.p
    sgrp2nmndlem3
    syl3anc
    ex
    pm2.61i
    @23
    @15
    @17
    vx
    vy
    cA
    cB
    cB
    cS
    cM
    c.op
    mgm2nsgrp.s
    mgm2nsgrp.b
    sgrp2nmnd.o
    sgrp2nmnd.p
    sgrp2nmndlem2
    @25
    @23
    @17
    wi
    @23
    @10
    @25
    @17
    @24
    @25
    @9
    @16
    cA
    cB
    @25
    cA
    cB
    cA
    cB
    c.op
    @26
    @26
    oveq12d
    @26
    eqeq12d
    syl5ib
    @27
    @23
    @17
    @28
    @21
    @21
    @29
    @17
    @30
    @30
    @31
    vx
    vy
    cA
    cB
    cB
    cS
    cM
    c.op
    mgm2nsgrp.s
    mgm2nsgrp.b
    sgrp2nmnd.o
    sgrp2nmnd.p
    sgrp2nmndlem3
    syl3anc
    ex
    pm2.61i
    jca
    jca31
    syl2an
    @2
    @8
    cA
    @4
    c.op
    co
    #
    cA
    wceq
    #
    cB
    @4
    c.op
    co
    #
    cB
    wceq
    #
    wa
    #
    vx
    cS
    wral
    #
    @19
    @2
    @7
    @36
    vx
    cS
    @7
    @6
    vy
    @22
    wral
    @2
    @36
    @6
    vy
    cS
    @22
    mgm2nsgrp.s
    raleqi
    @6
    @33
    @35
    vy
    cA
    cB
    cV
    cW
    @3
    cA
    wceq
    #
    @5
    @32
    @3
    cA
    @3
    cA
    @4
    c.op
    oveq1
    @38
    id
    eqeq12d
    @3
    cB
    wceq
    #
    @5
    @34
    @3
    cB
    @3
    cB
    @4
    c.op
    oveq1
    @39
    id
    eqeq12d
    ralprg
    syl5bb
    ralbidv
    @37
    @36
    vx
    @22
    wral
    @2
    @19
    @36
    vx
    cS
    @22
    mgm2nsgrp.s
    raleqi
    @36
    @13
    @18
    vx
    cA
    cB
    cV
    cW
    @4
    cA
    wceq
    #
    @33
    @10
    @35
    @12
    @40
    @32
    @9
    cA
    @4
    cA
    cA
    c.op
    oveq2
    eqeq1d
    @40
    @34
    @11
    cB
    @4
    cA
    cB
    c.op
    oveq2
    eqeq1d
    anbi12d
    @4
    cB
    wceq
    #
    @33
    @15
    @35
    @17
    @41
    @32
    @14
    cA
    @4
    cB
    cA
    c.op
    oveq2
    eqeq1d
    @41
    @34
    @16
    cB
    @4
    cB
    cB
    c.op
    oveq2
    eqeq1d
    anbi12d
    ralprg
    syl5bb
    bitrd
    mpbird
end
