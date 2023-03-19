include "ccring.mm"
include "wcel.mm"
include "cidl.mm"
include "cfv.mm"
include "wss.mm"
include "cv.mm"
include "co.mm"
include "wral.mm"
include "wa.mm"
include "w3a.mm"
include "crngo.mm"
include "wb.mm"
include "crngorngo.mm"
include "isidl.mm"
include "syl.mm"
include "ssel2.mm"
include "wi.mm"
include "crngocom.mm"
include "eleq1d.mm"
include "biimprd.mm"
include "3expa.mm"
include "pm4.71d.mm"
include "bicomd.mm"
include "ralbidva.mm"
include "anbi2d.mm"
include "sylan2.mm"
include "anassrs.mm"
include "adantrr.mm"
include "pm5.32da.mm"
include "df-3an.mm"
include "3bitr4g.mm"
include "bitrd.mm"

theorem isidlc
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let cR: class R
  let cG: class G
  let cH: class H
  let cI: class I
  let cX: class X
  let cZ: class Z
  let vr: setvar r
  let vi: setvar i
  assume idlval.1: |- G = ( 1st ` R )
  assume idlval.2: |- H = ( 2nd ` R )
  assume idlval.3: |- X = ran G
  assume idlval.4: |- Z = ( GId ` G )

  disjoint R x
  disjoint R y
  disjoint R z
  disjoint x y
  disjoint x z
  disjoint y z
  disjoint X z
  disjoint I x
  disjoint I y
  disjoint I z
  disjoint X x
  disjoint R r
  disjoint R i
  disjoint r x
  disjoint r y
  disjoint r z
  disjoint i r
  disjoint i x
  disjoint i y
  disjoint i z
  disjoint X r
  disjoint X i
  disjoint I i
  disjoint Z r
  disjoint Z i
  disjoint G r
  disjoint G i
  disjoint H r
  disjoint H i
  assert |- ( R e. CRingOps -> ( I e. ( Idl ` R ) <-> ( I C_ X /\ Z e. I /\ A. x e. I ( A. y e. I ( x G y ) e. I /\ A. z e. X ( z H x ) e. I ) ) ) )

  proof
    cR
    ccring
    wcel
    #
    cI
    cR
    cidl
    cfv
    wcel
    #
    cI
    cX
    wss
    #
    cZ
    cI
    wcel
    #
    vx
    cv
    #
    vy
    cv
    cG
    co
    cI
    wcel
    vy
    cI
    wral
    #
    vz
    cv
    #
    @4
    cH
    co
    #
    cI
    wcel
    #
    @4
    @6
    cH
    co
    #
    cI
    wcel
    #
    wa
    #
    vz
    cX
    wral
    #
    wa
    #
    vx
    cI
    wral
    #
    w3a
    #
    @2
    @3
    @5
    @8
    vz
    cX
    wral
    #
    wa
    #
    vx
    cI
    wral
    #
    w3a
    #
    @0
    cR
    crngo
    wcel
    @1
    @15
    wb
    cR
    crngorngo
    vx
    vy
    vz
    cR
    cG
    cH
    cI
    cX
    cZ
    idlval.1
    idlval.2
    idlval.3
    idlval.4
    isidl
    syl
    @0
    @2
    @3
    wa
    #
    @14
    wa
    @20
    @18
    wa
    @15
    @19
    @0
    @20
    @14
    @18
    @0
    @2
    @14
    @18
    wb
    @3
    @0
    @2
    wa
    @13
    @17
    vx
    cI
    @0
    @2
    @4
    cI
    wcel
    #
    @13
    @17
    wb
    #
    @2
    @21
    wa
    @0
    @4
    cX
    wcel
    #
    @22
    cI
    cX
    @4
    ssel2
    @0
    @23
    wa
    #
    @12
    @16
    @5
    @24
    @11
    @8
    vz
    cX
    @24
    @6
    cX
    wcel
    #
    wa
    #
    @8
    @11
    @26
    @8
    @10
    @0
    @23
    @25
    @8
    @10
    wi
    @0
    @23
    @25
    w3a
    #
    @10
    @8
    @27
    @9
    @7
    cI
    @4
    @6
    cR
    cG
    cH
    cX
    idlval.1
    idlval.2
    idlval.3
    crngocom
    eleq1d
    biimprd
    3expa
    pm4.71d
    bicomd
    ralbidva
    anbi2d
    sylan2
    anassrs
    ralbidva
    adantrr
    pm5.32da
    @2
    @3
    @14
    df-3an
    @2
    @3
    @18
    df-3an
    3bitr4g
    bitrd
end
