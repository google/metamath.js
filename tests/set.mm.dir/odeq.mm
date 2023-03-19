include "cgrp.mm"
include "wcel.mm"
include "cn0.mm"
include "w3a.mm"
include "cfv.mm"
include "wceq.mm"
include "cv.mm"
include "cdvds.mm"
include "wbr.mm"
include "co.mm"
include "wb.mm"
include "wral.mm"
include "wi.mm"
include "wa.mm"
include "cz.mm"
include "nn0z.mm"
include "oddvds.mm"
include "syl3an3.mm"
include "3expa.mm"
include "ralrimiva.mm"
include "breq1.mm"
include "bibi1d.mm"
include "ralbidv.mm"
include "syl5ibrcom.mm"
include "3adant3.mm"
include "simpl3.mm"
include "simpl2.mm"
include "odcl.mm"
include "syl.mm"
include "odid.mm"
include "3ad2ant2.mm"
include "breq2.mm"
include "oveq1.mm"
include "eqeq1d.mm"
include "bibi12d.mm"
include "rspcva.mm"
include "sylan.mm"
include "mpbird.mm"
include "iddvds.mm"
include "3syl.mm"
include "3ad2antl3.mm"
include "mpbid.mm"
include "adantr.mm"
include "dvdseq.mm"
include "syl22anc.mm"
include "ex.mm"
include "impbid.mm"

theorem odeq
  let vy: setvar y
  let cA: class A
  let c.x: class .x.
  let cG: class G
  let cN: class N
  let cO: class O
  let cX: class X
  let c.0: class .0.
  let vw: setvar w
  let vz: setvar z
  let vx: setvar x
  assume odcl.1: |- X = ( Base ` G )
  assume odcl.2: |- O = ( od ` G )
  assume odid.3: |- .x. = ( .g ` G )
  assume odid.4: |- .0. = ( 0g ` G )

  disjoint .0. y
  disjoint A y
  disjoint N y
  disjoint O y
  disjoint .x. y
  disjoint G y
  disjoint X y
  disjoint w y
  disjoint w z
  disjoint y z
  disjoint x y
  disjoint A x
  disjoint O x
  disjoint x z
  disjoint G x
  disjoint G z
  disjoint X x
  assert |- ( ( G e. Grp /\ A e. X /\ N e. NN0 ) -> ( N = ( O ` A ) <-> A. y e. NN0 ( N || y <-> ( y .x. A ) = .0. ) ) )

  proof
    cG
    cgrp
    wcel
    #
    cA
    cX
    wcel
    #
    cN
    cn0
    wcel
    #
    w3a
    #
    cN
    cA
    cO
    cfv
    #
    wceq
    #
    cN
    vy
    cv
    #
    cdvds
    wbr
    #
    @6
    cA
    c.x
    co
    #
    c.0
    wceq
    #
    wb
    #
    vy
    cn0
    wral
    #
    @0
    @1
    @5
    @11
    wi
    @2
    @0
    @1
    wa
    #
    @11
    @5
    @4
    @6
    cdvds
    wbr
    #
    @9
    wb
    #
    vy
    cn0
    wral
    @12
    @14
    vy
    cn0
    @0
    @1
    @6
    cn0
    wcel
    #
    @14
    @15
    @0
    @1
    @6
    cz
    wcel
    @14
    @6
    nn0z
    cA
    c.x
    cG
    @6
    cO
    cX
    c.0
    odcl.1
    odcl.2
    odid.3
    odid.4
    oddvds
    syl3an3
    3expa
    ralrimiva
    @5
    @10
    @14
    vy
    cn0
    @5
    @7
    @13
    @9
    cN
    @4
    @6
    cdvds
    breq1
    bibi1d
    ralbidv
    syl5ibrcom
    3adant3
    @3
    @11
    @5
    @3
    @11
    wa
    #
    @2
    @4
    cn0
    wcel
    #
    cN
    @4
    cdvds
    wbr
    #
    @4
    cN
    cdvds
    wbr
    #
    @5
    @0
    @1
    @2
    @11
    simpl3
    #
    @16
    @1
    @17
    @0
    @1
    @2
    @11
    simpl2
    #
    cA
    cG
    cO
    cX
    odcl.1
    odcl.2
    odcl
    #
    syl
    @16
    @18
    @4
    cA
    c.x
    co
    #
    c.0
    wceq
    #
    @16
    @1
    @24
    @21
    cA
    c.x
    cG
    cO
    cX
    c.0
    odcl.1
    odcl.2
    odid.3
    odid.4
    odid
    syl
    @3
    @17
    @11
    @18
    @24
    wb
    #
    @1
    @0
    @17
    @2
    @22
    3ad2ant2
    @10
    @25
    vy
    @4
    cn0
    @6
    @4
    wceq
    #
    @7
    @18
    @9
    @24
    @6
    @4
    cN
    cdvds
    breq2
    @26
    @8
    @23
    c.0
    @6
    @4
    cA
    c.x
    oveq1
    eqeq1d
    bibi12d
    rspcva
    sylan
    mpbird
    @16
    @19
    cN
    cA
    c.x
    co
    #
    c.0
    wceq
    #
    @16
    cN
    cN
    cdvds
    wbr
    #
    @28
    @16
    @2
    cN
    cz
    wcel
    #
    @29
    @20
    cN
    nn0z
    #
    cN
    iddvds
    3syl
    @2
    @0
    @11
    @29
    @28
    wb
    #
    @1
    @10
    @32
    vy
    cN
    cn0
    @6
    cN
    wceq
    #
    @7
    @29
    @9
    @28
    @6
    cN
    cN
    cdvds
    breq2
    @33
    @8
    @27
    c.0
    @6
    cN
    cA
    c.x
    oveq1
    eqeq1d
    bibi12d
    rspcva
    3ad2antl3
    mpbid
    @3
    @19
    @28
    wb
    #
    @11
    @2
    @0
    @1
    @30
    @34
    @31
    cA
    c.x
    cG
    cN
    cO
    cX
    c.0
    odcl.1
    odcl.2
    odid.3
    odid.4
    oddvds
    syl3an3
    adantr
    mpbird
    cN
    @4
    dvdseq
    syl22anc
    ex
    impbid
end
