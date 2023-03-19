include "cmnd.mm"
include "wcel.mm"
include "wss.mm"
include "w3a.mm"
include "cv.mm"
include "co.mm"
include "wral.mm"
include "wa.mm"
include "cplusg.mm"
include "cfv.mm"
include "cbs.mm"
include "simplr.mm"
include "simprl.mm"
include "wceq.mm"
include "simpll2.mm"
include "ressbas2.mm"
include "syl.mm"
include "eleqtrd.mm"
include "simprr.mm"
include "eqid.mm"
include "mndcl.mm"
include "syl3anc.mm"
include "cvv.mm"
include "fvex.mm"
include "eqeltri.mm"
include "ssex.mm"
include "3ad2ant2.mm"
include "ressplusg.mm"
include "ad2antrr.mm"
include "oveqd.mm"
include "3eltr4d.mm"
include "ralrimivva.mm"
include "simpl2.mm"
include "adantr.mm"
include "ovrspc2v.mm"
include "ancoms.mm"
include "3impb.mm"
include "3adant1l.mm"
include "sseld.mm"
include "3anim123d.mm"
include "imp.mm"
include "simpl1.mm"
include "mndass.mm"
include "sylan.mm"
include "syldan.mm"
include "simpl3.mm"
include "sselda.mm"
include "mndlid.mm"
include "mndrid.mm"
include "ismndd.mm"
include "impbida.mm"

theorem issubmnd
  let vx: setvar x
  let vy: setvar y
  let cB: class B
  let c.pl: class .+
  let cS: class S
  let cG: class G
  let cH: class H
  let c.0: class .0.
  let vu: setvar u
  let vv: setvar v
  let vw: setvar w
  assume issubmnd.b: |- B = ( Base ` G )
  assume issubmnd.p: |- .+ = ( +g ` G )
  assume issubmnd.z: |- .0. = ( 0g ` G )
  assume issubmnd.h: |- H = ( G |`s S )

  disjoint x y
  disjoint B x
  disjoint B y
  disjoint G x
  disjoint G y
  disjoint H x
  disjoint H y
  disjoint .+ x
  disjoint .+ y
  disjoint S x
  disjoint S y
  disjoint .0. x
  disjoint .0. y
  disjoint u v
  disjoint u w
  disjoint u x
  disjoint u y
  disjoint B u
  disjoint v w
  disjoint v x
  disjoint v y
  disjoint B v
  disjoint w x
  disjoint w y
  disjoint B w
  disjoint G u
  disjoint G v
  disjoint G w
  disjoint H u
  disjoint H v
  disjoint H w
  disjoint .+ u
  disjoint .+ v
  disjoint .+ w
  disjoint S u
  disjoint S v
  disjoint S w
  disjoint .0. u
  disjoint .0. v
  disjoint .0. w
  assert |- ( ( G e. Mnd /\ S C_ B /\ .0. e. S ) -> ( H e. Mnd <-> A. x e. S A. y e. S ( x .+ y ) e. S ) )

  proof
    cG
    cmnd
    wcel
    #
    cS
    cB
    wss
    #
    c.0
    cS
    wcel
    #
    w3a
    #
    cH
    cmnd
    wcel
    #
    vx
    cv
    #
    vy
    cv
    #
    c.pl
    co
    #
    cS
    wcel
    #
    vy
    cS
    wral
    vx
    cS
    wral
    #
    @3
    @4
    wa
    #
    @8
    vx
    vy
    cS
    cS
    @10
    @5
    cS
    wcel
    #
    @6
    cS
    wcel
    #
    wa
    #
    wa
    #
    @5
    @6
    cH
    cplusg
    cfv
    #
    co
    #
    cH
    cbs
    cfv
    #
    @7
    cS
    @14
    @4
    @5
    @17
    wcel
    @6
    @17
    wcel
    @16
    @17
    wcel
    @3
    @4
    @13
    simplr
    @14
    @5
    cS
    @17
    @10
    @11
    @12
    simprl
    @14
    @1
    cS
    @17
    wceq
    #
    @0
    @1
    @2
    @4
    @13
    simpll2
    cS
    cB
    cH
    cG
    issubmnd.h
    issubmnd.b
    ressbas2
    #
    syl
    #
    eleqtrd
    @14
    @6
    cS
    @17
    @10
    @11
    @12
    simprr
    @20
    eleqtrd
    @17
    @15
    cH
    @5
    @6
    @17
    eqid
    @15
    eqid
    mndcl
    syl3anc
    @14
    c.pl
    @15
    @5
    @6
    @3
    c.pl
    @15
    wceq
    #
    @4
    @13
    @3
    cS
    cvv
    wcel
    #
    @21
    @1
    @0
    @22
    @2
    cS
    cB
    cB
    cG
    cbs
    cfv
    cvv
    issubmnd.b
    cG
    cbs
    fvex
    eqeltri
    ssex
    3ad2ant2
    cS
    c.pl
    cG
    cH
    cvv
    issubmnd.h
    issubmnd.p
    ressplusg
    syl
    #
    ad2antrr
    oveqd
    @20
    3eltr4d
    ralrimivva
    @3
    @9
    wa
    #
    vu
    vv
    vw
    cS
    c.pl
    cH
    c.0
    @24
    @1
    @18
    @0
    @1
    @2
    @9
    simpl2
    #
    @19
    syl
    @3
    @21
    @9
    @23
    adantr
    @9
    vu
    cv
    #
    cS
    wcel
    #
    vv
    cv
    #
    cS
    wcel
    #
    @26
    @28
    c.pl
    co
    #
    cS
    wcel
    #
    @3
    @9
    @27
    @29
    @31
    @27
    @29
    wa
    @9
    @31
    vx
    vy
    cS
    cS
    cS
    c.pl
    @26
    @28
    ovrspc2v
    ancoms
    3impb
    3adant1l
    @24
    @27
    @29
    vw
    cv
    #
    cS
    wcel
    #
    w3a
    #
    @26
    cB
    wcel
    #
    @28
    cB
    wcel
    #
    @32
    cB
    wcel
    #
    w3a
    #
    @30
    @32
    c.pl
    co
    @26
    @28
    @32
    c.pl
    co
    c.pl
    co
    wceq
    #
    @24
    @34
    @38
    @24
    @27
    @35
    @29
    @36
    @33
    @37
    @24
    cS
    cB
    @26
    @25
    sseld
    @24
    cS
    cB
    @28
    @25
    sseld
    @24
    cS
    cB
    @32
    @25
    sseld
    3anim123d
    imp
    @24
    @0
    @38
    @39
    @0
    @1
    @2
    @9
    simpl1
    #
    cB
    c.pl
    cG
    @26
    @28
    @32
    issubmnd.b
    issubmnd.p
    mndass
    sylan
    syldan
    @0
    @1
    @2
    @9
    simpl3
    @24
    @27
    @35
    c.0
    @26
    c.pl
    co
    @26
    wceq
    #
    @24
    cS
    cB
    @26
    @25
    sselda
    #
    @24
    @0
    @35
    @41
    @40
    cB
    c.pl
    cG
    @26
    c.0
    issubmnd.b
    issubmnd.p
    issubmnd.z
    mndlid
    sylan
    syldan
    @24
    @27
    @35
    @26
    c.0
    c.pl
    co
    @26
    wceq
    #
    @42
    @24
    @0
    @35
    @43
    @40
    cB
    c.pl
    cG
    @26
    c.0
    issubmnd.b
    issubmnd.p
    issubmnd.z
    mndrid
    sylan
    syldan
    ismndd
    impbida
end
