include "cgrp.mm"
include "wcel.mm"
include "cz.mm"
include "w3a.mm"
include "cfv.mm"
include "cn.mm"
include "cdvds.mm"
include "wbr.mm"
include "co.mm"
include "wceq.mm"
include "wb.mm"
include "cc0.mm"
include "wa.mm"
include "cmo.mm"
include "simpr.mm"
include "simpl3.mm"
include "dvdsval3.mm"
include "syl2anc.mm"
include "simpl2.mm"
include "mulg0.mm"
include "syl.mm"
include "oveq1.mm"
include "eqeq1d.mm"
include "syl5ibrcom.mm"
include "wn.mm"
include "cle.mm"
include "wi.mm"
include "clt.mm"
include "cr.mm"
include "crp.mm"
include "zred.mm"
include "nnrpd.mm"
include "modlt.mm"
include "zmodcld.mm"
include "nn0red.mm"
include "nnred.mm"
include "ltnled.mm"
include "mpbid.mm"
include "c1.mm"
include "cfz.mm"
include "odlem2.mm"
include "elfzle2.mm"
include "3com23.mm"
include "3expia.mm"
include "con3d.mm"
include "impancom.mm"
include "cn0.mm"
include "wo.mm"
include "elnn0.mm"
include "sylib.mm"
include "ord.mm"
include "syld.mm"
include "impbid.mm"
include "odmod.mm"
include "3bitrd.mm"
include "breq1d.mm"
include "0dvds.mm"
include "wne.mm"
include "odnncl.mm"
include "nnne0d.mm"
include "expr.mm"
include "necon4d.mm"
include "odcl.mm"
include "3ad2ant2.mm"
include "mpjaodan.mm"

theorem oddvds
  let cA: class A
  let c.x: class .x.
  let cG: class G
  let cN: class N
  let cO: class O
  let cX: class X
  let c.0: class .0.
  let vw: setvar w
  let vy: setvar y
  let vz: setvar z
  let vx: setvar x
  assume odcl.1: |- X = ( Base ` G )
  assume odcl.2: |- O = ( od ` G )
  assume odid.3: |- .x. = ( .g ` G )
  assume odid.4: |- .0. = ( 0g ` G )


  assert |- ( ( G e. Grp /\ A e. X /\ N e. ZZ ) -> ( ( O ` A ) || N <-> ( N .x. A ) = .0. ) )

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
    cz
    wcel
    #
    w3a
    #
    cA
    cO
    cfv
    #
    cn
    wcel
    #
    @4
    cN
    cdvds
    wbr
    #
    cN
    cA
    c.x
    co
    #
    c.0
    wceq
    #
    wb
    @4
    cc0
    wceq
    #
    @3
    @5
    wa
    #
    @6
    cN
    @4
    cmo
    co
    #
    cc0
    wceq
    #
    @11
    cA
    c.x
    co
    #
    c.0
    wceq
    #
    @8
    @10
    @5
    @2
    @6
    @12
    wb
    @3
    @5
    simpr
    #
    @0
    @1
    @2
    @5
    simpl3
    #
    @4
    cN
    dvdsval3
    syl2anc
    @10
    @12
    @14
    @10
    @14
    @12
    cc0
    cA
    c.x
    co
    #
    c.0
    wceq
    #
    @10
    @1
    @18
    @0
    @1
    @2
    @5
    simpl2
    #
    cX
    c.x
    cG
    cA
    c.0
    odcl.1
    odid.4
    odid.3
    mulg0
    #
    syl
    @12
    @13
    @17
    c.0
    @11
    cc0
    cA
    c.x
    oveq1
    eqeq1d
    syl5ibrcom
    @10
    @14
    @11
    cn
    wcel
    #
    wn
    #
    @12
    @10
    @1
    @4
    @11
    cle
    wbr
    #
    wn
    #
    @14
    @22
    wi
    @19
    @10
    @11
    @4
    clt
    wbr
    #
    @24
    @10
    cN
    cr
    wcel
    @4
    crp
    wcel
    @25
    @10
    cN
    @16
    zred
    @10
    @4
    @15
    nnrpd
    cN
    @4
    modlt
    syl2anc
    @10
    @11
    @4
    @10
    @11
    @10
    cN
    @4
    @16
    @15
    zmodcld
    #
    nn0red
    @10
    @4
    @15
    nnred
    ltnled
    mpbid
    @1
    @14
    @24
    @22
    @1
    @14
    wa
    @21
    @23
    @1
    @14
    @21
    @23
    @1
    @21
    @14
    @23
    @1
    @21
    @14
    w3a
    @4
    c1
    @11
    cfz
    co
    wcel
    @23
    cA
    c.x
    cG
    @11
    cO
    cX
    c.0
    odcl.1
    odcl.2
    odid.3
    odid.4
    odlem2
    @4
    c1
    @11
    elfzle2
    syl
    3com23
    3expia
    con3d
    impancom
    syl2anc
    @10
    @21
    @12
    @10
    @11
    cn0
    wcel
    @21
    @12
    wo
    @26
    @11
    elnn0
    sylib
    ord
    syld
    impbid
    @10
    @13
    @7
    c.0
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
    odmod
    eqeq1d
    3bitrd
    @3
    @9
    wa
    #
    @6
    cc0
    cN
    cdvds
    wbr
    #
    cN
    cc0
    wceq
    #
    @8
    @27
    @4
    cc0
    cN
    cdvds
    @3
    @9
    simpr
    breq1d
    @27
    @2
    @28
    @29
    wb
    @0
    @1
    @2
    @9
    simpl3
    cN
    0dvds
    syl
    @27
    @29
    @8
    @27
    @8
    @29
    @18
    @27
    @1
    @18
    @0
    @1
    @2
    @9
    simpl2
    @20
    syl
    @29
    @7
    @17
    c.0
    cN
    cc0
    cA
    c.x
    oveq1
    eqeq1d
    syl5ibrcom
    @3
    @8
    @9
    @29
    @3
    @8
    wa
    cN
    cc0
    @4
    cc0
    @3
    cN
    cc0
    wne
    #
    @8
    @4
    cc0
    wne
    #
    @3
    @30
    @8
    @31
    @3
    @30
    @8
    wa
    wa
    @4
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
    odnncl
    nnne0d
    expr
    impancom
    necon4d
    impancom
    impbid
    3bitrd
    @3
    @4
    cn0
    wcel
    #
    @5
    @9
    wo
    @1
    @0
    @32
    @2
    cA
    cG
    cO
    cX
    odcl.1
    odcl.2
    odcl
    3ad2ant2
    @4
    elnn0
    sylib
    mpjaodan
end
