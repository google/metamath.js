include "cgrp.mm"
include "wcel.mm"
include "cdvds.mm"
include "wbr.mm"
include "w3a.mm"
include "cv.mm"
include "cmul.mm"
include "co.mm"
include "wceq.mm"
include "cz.mm"
include "wrex.mm"
include "wa.mm"
include "simp3.mm"
include "dvdszrcl.mm"
include "divides.mm"
include "biadan2.mm"
include "sylib.mm"
include "simprd.mm"
include "simpl1.mm"
include "simpr.mm"
include "simplld.mm"
include "adantr.mm"
include "simpl2.mm"
include "mulgass.mm"
include "syl13anc.mm"
include "gexid.mm"
include "syl.mm"
include "oveq2d.mm"
include "mulgz.mm"
include "3ad2antl1.mm"
include "3eqtrd.mm"
include "oveq1.mm"
include "eqeq1d.mm"
include "syl5ibcom.mm"
include "rexlimdva.mm"
include "mpd.mm"

theorem gexdvdsi
  let cA: class A
  let c.x: class .x.
  let cE: class E
  let cG: class G
  let cN: class N
  let cX: class X
  let c.0: class .0.
  let vx: setvar x
  let vy: setvar y
  let cV: class V
  assume gexcl.1: |- X = ( Base ` G )
  assume gexcl.2: |- E = ( gEx ` G )
  assume gexid.3: |- .x. = ( .g ` G )
  assume gexid.4: |- .0. = ( 0g ` G )


  assert |- ( ( G e. Grp /\ A e. X /\ E || N ) -> ( N .x. A ) = .0. )

  proof
    cG
    cgrp
    wcel
    #
    cA
    cX
    wcel
    #
    cE
    cN
    cdvds
    wbr
    #
    w3a
    #
    vx
    cv
    #
    cE
    cmul
    co
    #
    cN
    wceq
    #
    vx
    cz
    wrex
    #
    cN
    cA
    c.x
    co
    #
    c.0
    wceq
    #
    @3
    cE
    cz
    wcel
    #
    cN
    cz
    wcel
    #
    wa
    #
    @7
    @3
    @2
    @12
    @7
    wa
    @0
    @1
    @2
    simp3
    @2
    @12
    @7
    cE
    cN
    dvdszrcl
    vx
    cE
    cN
    divides
    biadan2
    sylib
    #
    simprd
    @3
    @6
    @9
    vx
    cz
    @3
    @4
    cz
    wcel
    #
    wa
    #
    @5
    cA
    c.x
    co
    #
    c.0
    wceq
    @6
    @9
    @15
    @16
    @4
    cE
    cA
    c.x
    co
    #
    c.x
    co
    #
    @4
    c.0
    c.x
    co
    #
    c.0
    @15
    @0
    @14
    @10
    @1
    @16
    @18
    wceq
    @0
    @1
    @2
    @14
    simpl1
    @3
    @14
    simpr
    @3
    @10
    @14
    @3
    @10
    @11
    @7
    @13
    simplld
    adantr
    @0
    @1
    @2
    @14
    simpl2
    #
    cX
    c.x
    cG
    @4
    cE
    cA
    gexcl.1
    gexid.3
    mulgass
    syl13anc
    @15
    @17
    c.0
    @4
    c.x
    @15
    @1
    @17
    c.0
    wceq
    @20
    cA
    c.x
    cE
    cG
    cX
    c.0
    gexcl.1
    gexcl.2
    gexid.3
    gexid.4
    gexid
    syl
    oveq2d
    @0
    @1
    @14
    @19
    c.0
    wceq
    @2
    cX
    c.x
    cG
    @4
    c.0
    gexcl.1
    gexid.3
    gexid.4
    mulgz
    3ad2antl1
    3eqtrd
    @6
    @16
    @8
    c.0
    @5
    cN
    cA
    c.x
    oveq1
    eqeq1d
    syl5ibcom
    rexlimdva
    mpd
end
