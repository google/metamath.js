include "chash.mm"
include "cfv.mm"
include "c2.mm"
include "wceq.mm"
include "wcel.mm"
include "wne.mm"
include "w3a.mm"
include "cv.mm"
include "cplusg.mm"
include "co.mm"
include "cpr.mm"
include "wrex.mm"
include "wral.mm"
include "cmnd.mm"
include "wnel.mm"
include "hashprdifel.mm"
include "wo.mm"
include "eqid.mm"
include "sgrp2nmndlem2.mm"
include "3adant3.mm"
include "simp3.mm"
include "eqnetrd.mm"
include "olcd.mm"
include "wb.mm"
include "oveq2.mm"
include "id.mm"
include "neeq12d.mm"
include "rexprg.mm"
include "mpbird.mm"
include "wn.mm"
include "sgrp2nmndlem3.mm"
include "wa.mm"
include "necom.mm"
include "df-ne.mm"
include "sylbb.mm"
include "3ad2ant3.mm"
include "adantr.mm"
include "eqeq1.mm"
include "adantl.mm"
include "mtbird.mm"
include "mpdan.mm"
include "neqned.mm"
include "orcd.mm"
include "oveq1.mm"
include "neeq1d.mm"
include "rexbidv.mm"
include "ralprg.mm"
include "mpbir2and.mm"
include "cbs.mm"
include "eqtr2i.mm"
include "isnmnd.mm"
include "3syl.mm"

theorem sgrp2nmndlem5
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
  assert |- ( ( # ` S ) = 2 -> M e/ Mnd )

  proof
    cS
    chash
    cfv
    c2
    wceq
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
    #
    vx
    cv
    #
    vy
    cv
    #
    cM
    cplusg
    cfv
    #
    co
    #
    @5
    wne
    #
    vy
    cA
    cB
    cpr
    #
    wrex
    #
    vx
    @9
    wral
    #
    cM
    cmnd
    wnel
    cA
    cB
    cS
    mgm2nsgrp.s
    hashprdifel
    @3
    @11
    cA
    @5
    @6
    co
    #
    @5
    wne
    #
    vy
    @9
    wrex
    #
    cB
    @5
    @6
    co
    #
    @5
    wne
    #
    vy
    @9
    wrex
    #
    @3
    @14
    cA
    cA
    @6
    co
    #
    cA
    wne
    #
    cA
    cB
    @6
    co
    #
    cB
    wne
    #
    wo
    #
    @3
    @21
    @19
    @3
    @20
    cA
    cB
    @0
    @1
    @20
    cA
    wceq
    @2
    vx
    vy
    cA
    cB
    cB
    cS
    cM
    @6
    mgm2nsgrp.s
    mgm2nsgrp.b
    sgrp2nmnd.o
    @6
    eqid
    #
    sgrp2nmndlem2
    3adant3
    @0
    @1
    @2
    simp3
    eqnetrd
    olcd
    @0
    @1
    @14
    @22
    wb
    @2
    @13
    @19
    @21
    vy
    cA
    cB
    cS
    cS
    @5
    cA
    wceq
    #
    @12
    @18
    @5
    cA
    @5
    cA
    cA
    @6
    oveq2
    @24
    id
    #
    neeq12d
    @5
    cB
    wceq
    #
    @12
    @20
    @5
    cB
    @5
    cB
    cA
    @6
    oveq2
    @26
    id
    #
    neeq12d
    rexprg
    3adant3
    mpbird
    @3
    @17
    cB
    cA
    @6
    co
    #
    cA
    wne
    #
    cB
    cB
    @6
    co
    #
    cB
    wne
    #
    wo
    #
    @3
    @29
    @31
    @3
    @28
    cA
    @3
    @28
    cB
    wceq
    #
    @28
    cA
    wceq
    #
    wn
    vx
    vy
    cA
    cB
    cA
    cS
    cM
    @6
    mgm2nsgrp.s
    mgm2nsgrp.b
    sgrp2nmnd.o
    @23
    sgrp2nmndlem3
    @3
    @33
    wa
    @34
    cB
    cA
    wceq
    #
    @3
    @35
    wn
    #
    @33
    @2
    @0
    @36
    @1
    @2
    cB
    cA
    wne
    @36
    cA
    cB
    necom
    cB
    cA
    df-ne
    sylbb
    3ad2ant3
    adantr
    @33
    @34
    @35
    wb
    @3
    @28
    cB
    cA
    eqeq1
    adantl
    mtbird
    mpdan
    neqned
    orcd
    @0
    @1
    @17
    @32
    wb
    @2
    @16
    @29
    @31
    vy
    cA
    cB
    cS
    cS
    @24
    @15
    @28
    @5
    cA
    @5
    cA
    cB
    @6
    oveq2
    @25
    neeq12d
    @26
    @15
    @30
    @5
    cB
    @5
    cB
    cB
    @6
    oveq2
    @27
    neeq12d
    rexprg
    3adant3
    mpbird
    @0
    @1
    @11
    @14
    @17
    wa
    wb
    @2
    @10
    @14
    @17
    vx
    cA
    cB
    cS
    cS
    @4
    cA
    wceq
    #
    @8
    @13
    vy
    @9
    @37
    @7
    @12
    @5
    @4
    cA
    @5
    @6
    oveq1
    neeq1d
    rexbidv
    @4
    cB
    wceq
    #
    @8
    @16
    vy
    @9
    @38
    @7
    @15
    @5
    @4
    cB
    @5
    @6
    oveq1
    neeq1d
    rexbidv
    ralprg
    3adant3
    mpbir2and
    vy
    vx
    @9
    cM
    @6
    cM
    cbs
    cfv
    cS
    @9
    mgm2nsgrp.b
    mgm2nsgrp.s
    eqtr2i
    @23
    isnmnd
    3syl
end
