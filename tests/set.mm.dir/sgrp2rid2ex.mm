include "chash.mm"
include "cfv.mm"
include "c2.mm"
include "wceq.mm"
include "wcel.mm"
include "wne.mm"
include "w3a.mm"
include "cv.mm"
include "co.mm"
include "wral.mm"
include "wrex.mm"
include "hashprdifel.mm"
include "simp1.mm"
include "simp2.mm"
include "simpl3.mm"
include "ralrimiva.mm"
include "wa.mm"
include "sgrp2rid2.mm"
include "wi.mm"
include "oveq2.mm"
include "eqeq1d.mm"
include "ralbidv.mm"
include "rspcv.mm"
include "adantr.mm"
include "mpd.mm"
include "3adant3.mm"
include "adantl.mm"
include "r19.26-3.mm"
include "syl3anbrc.mm"
include "3jca.mm"
include "neeq1.mm"
include "biidd.mm"
include "3anbi123d.mm"
include "neeq2.mm"
include "rspc2ev.mm"
include "3syl.mm"

theorem sgrp2rid2ex
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let cA: class A
  let cB: class B
  let cS: class S
  let cM: class M
  let c.op: class .o.
  let cC: class C
  let cV: class V
  let cW: class W
  let va: setvar a
  let vb: setvar b
  assume mgm2nsgrp.s: |- S = { A , B }
  assume mgm2nsgrp.b: |- ( Base ` M ) = S
  assume sgrp2nmnd.o: |- ( +g ` M ) = ( x e. S , y e. S |-> if ( x = A , A , B ) )
  assume sgrp2nmnd.p: |- .o. = ( +g ` M )

  disjoint x y
  disjoint .o. x
  disjoint .o. y
  disjoint A z
  disjoint B z
  disjoint S z
  disjoint .o. z
  disjoint x z
  disjoint y z
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
  disjoint V x
  disjoint W x
  disjoint M a
  disjoint M b
  disjoint a b
  disjoint S a
  disjoint S b
  disjoint a x
  disjoint a y
  disjoint b x
  disjoint b y
  assert |- ( ( # ` S ) = 2 -> E. x e. S E. z e. S A. y e. S ( x =/= z /\ ( y .o. x ) = y /\ ( y .o. z ) = y ) )

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
    @0
    @1
    @2
    vy
    cv
    #
    cA
    c.op
    co
    #
    @4
    wceq
    #
    @4
    cB
    c.op
    co
    #
    @4
    wceq
    #
    w3a
    #
    vy
    cS
    wral
    #
    w3a
    vx
    cv
    #
    vz
    cv
    #
    wne
    #
    @4
    @11
    c.op
    co
    #
    @4
    wceq
    #
    @4
    @12
    c.op
    co
    #
    @4
    wceq
    #
    w3a
    #
    vy
    cS
    wral
    #
    vz
    cS
    wrex
    vx
    cS
    wrex
    cA
    cB
    cS
    mgm2nsgrp.s
    hashprdifel
    @3
    @0
    @1
    @10
    @0
    @1
    @2
    simp1
    @0
    @1
    @2
    simp2
    @3
    @2
    vy
    cS
    wral
    @6
    vy
    cS
    wral
    #
    @8
    vy
    cS
    wral
    #
    @10
    @3
    @2
    vy
    cS
    @0
    @1
    @2
    @4
    cS
    wcel
    simpl3
    ralrimiva
    @0
    @1
    @20
    @2
    @0
    @1
    wa
    #
    @15
    vy
    cS
    wral
    #
    vx
    cS
    wral
    #
    @20
    vx
    vy
    cA
    cB
    cS
    cM
    cS
    cS
    c.op
    mgm2nsgrp.s
    mgm2nsgrp.b
    sgrp2nmnd.o
    sgrp2nmnd.p
    sgrp2rid2
    #
    @0
    @24
    @20
    wi
    @1
    @23
    @20
    vx
    cA
    cS
    @11
    cA
    wceq
    #
    @15
    @6
    vy
    cS
    @26
    @14
    @5
    @4
    @11
    cA
    @4
    c.op
    oveq2
    eqeq1d
    #
    ralbidv
    rspcv
    adantr
    mpd
    3adant3
    @0
    @1
    @21
    @2
    @22
    @24
    @21
    @25
    @1
    @24
    @21
    wi
    @0
    @23
    @21
    vx
    cB
    cS
    @11
    cB
    wceq
    #
    @15
    @8
    vy
    cS
    @28
    @14
    @7
    @4
    @11
    cB
    @4
    c.op
    oveq2
    eqeq1d
    ralbidv
    rspcv
    adantl
    mpd
    3adant3
    @2
    @6
    @8
    vy
    cS
    r19.26-3
    syl3anbrc
    3jca
    @19
    @10
    cA
    @12
    wne
    #
    @6
    @17
    w3a
    #
    vy
    cS
    wral
    vx
    vz
    cA
    cB
    cS
    cS
    @26
    @18
    @30
    vy
    cS
    @26
    @13
    @29
    @15
    @6
    @17
    @17
    @11
    cA
    @12
    neeq1
    @27
    @26
    @17
    biidd
    3anbi123d
    ralbidv
    @12
    cB
    wceq
    #
    @30
    @9
    vy
    cS
    @31
    @29
    @2
    @6
    @6
    @17
    @8
    @12
    cB
    cA
    neeq2
    @31
    @6
    biidd
    @31
    @16
    @7
    @4
    @12
    cB
    @4
    c.op
    oveq2
    eqeq1d
    3anbi123d
    ralbidv
    rspc2ev
    3syl
end
