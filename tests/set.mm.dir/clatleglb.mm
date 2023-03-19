include "ccla.mm"
include "wcel.mm"
include "wss.mm"
include "w3a.mm"
include "cfv.mm"
include "wbr.mm"
include "cv.mm"
include "wral.mm"
include "wa.mm"
include "clatglble.mm"
include "3expa.mm"
include "3adantl2.mm"
include "clat.mm"
include "wi.mm"
include "simpl1.mm"
include "clatl.mm"
include "syl.mm"
include "simpl2.mm"
include "clatglbcl.mm"
include "3adant2.mm"
include "adantr.mm"
include "ssel.mm"
include "3ad2ant3.mm"
include "imp.mm"
include "lattr.mm"
include "syl13anc.mm"
include "mpan2d.mm"
include "ralrimdva.mm"
include "clatglb.mm"
include "simprd.mm"
include "wceq.mm"
include "breq1.mm"
include "ralbidv.mm"
include "imbi12d.mm"
include "rspccv.mm"
include "ex.mm"
include "com23.mm"
include "3imp.mm"
include "impbid.mm"

theorem clatleglb
  let vy: setvar y
  let cB: class B
  let cS: class S
  let cG: class G
  let cK: class K
  let c.le: class .<_
  let cX: class X
  let vz: setvar z
  assume clatglb.b: |- B = ( Base ` K )
  assume clatglb.l: |- .<_ = ( le ` K )
  assume clatglb.g: |- G = ( glb ` K )

  disjoint B y
  disjoint G y
  disjoint K y
  disjoint .<_ y
  disjoint S y
  disjoint X y
  disjoint y z
  disjoint B z
  disjoint G z
  disjoint K z
  disjoint .<_ z
  disjoint S z
  disjoint X z
  assert |- ( ( K e. CLat /\ X e. B /\ S C_ B ) -> ( X .<_ ( G ` S ) <-> A. y e. S X .<_ y ) )

  proof
    cK
    ccla
    wcel
    #
    cX
    cB
    wcel
    #
    cS
    cB
    wss
    #
    w3a
    #
    cX
    cS
    cG
    cfv
    #
    c.le
    wbr
    #
    cX
    vy
    cv
    #
    c.le
    wbr
    #
    vy
    cS
    wral
    #
    @3
    @5
    @7
    vy
    cS
    @3
    @6
    cS
    wcel
    #
    wa
    #
    @5
    @4
    @6
    c.le
    wbr
    #
    @7
    @0
    @2
    @9
    @11
    @1
    @0
    @2
    @9
    @11
    cB
    cS
    cG
    cK
    c.le
    @6
    clatglb.b
    clatglb.l
    clatglb.g
    clatglble
    3expa
    3adantl2
    @10
    cK
    clat
    wcel
    #
    @1
    @4
    cB
    wcel
    #
    @6
    cB
    wcel
    #
    @5
    @11
    wa
    @7
    wi
    @10
    @0
    @12
    @0
    @1
    @2
    @9
    simpl1
    cK
    clatl
    syl
    @0
    @1
    @2
    @9
    simpl2
    @3
    @13
    @9
    @0
    @2
    @13
    @1
    cB
    cS
    cG
    cK
    clatglb.b
    clatglb.g
    clatglbcl
    3adant2
    adantr
    @3
    @9
    @14
    @2
    @0
    @9
    @14
    wi
    @1
    cS
    cB
    @6
    ssel
    3ad2ant3
    imp
    cB
    cK
    c.le
    cX
    @4
    @6
    clatglb.b
    clatglb.l
    lattr
    syl13anc
    mpan2d
    ralrimdva
    @0
    @1
    @2
    @8
    @5
    wi
    #
    @0
    @2
    @1
    @15
    @0
    @2
    @1
    @15
    wi
    #
    @0
    @2
    wa
    #
    vz
    cv
    #
    @6
    c.le
    wbr
    #
    vy
    cS
    wral
    #
    @18
    @4
    c.le
    wbr
    #
    wi
    #
    vz
    cB
    wral
    #
    @16
    @17
    @11
    vy
    cS
    wral
    @23
    vy
    vz
    cB
    cS
    cG
    cK
    c.le
    clatglb.b
    clatglb.l
    clatglb.g
    clatglb
    simprd
    @22
    @15
    vz
    cX
    cB
    @18
    cX
    wceq
    #
    @20
    @8
    @21
    @5
    @24
    @19
    @7
    vy
    cS
    @18
    cX
    @6
    c.le
    breq1
    ralbidv
    @18
    cX
    @4
    c.le
    breq1
    imbi12d
    rspccv
    syl
    ex
    com23
    3imp
    impbid
end
