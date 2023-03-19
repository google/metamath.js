include "cdrng.mm"
include "wcel.mm"
include "crngo.mm"
include "wne.mm"
include "cv.mm"
include "co.mm"
include "wceq.mm"
include "csn.mm"
include "cdif.mm"
include "wrex.mm"
include "wral.mm"
include "wa.mm"
include "isdrngo2.mm"
include "wb.mm"
include "eldifi.mm"
include "wss.mm"
include "wi.mm"
include "difss.mm"
include "ssrexv.mm"
include "ax-mp.mm"
include "neeq1.mm"
include "biimparc.mm"
include "rngolz.mm"
include "oveq1.mm"
include "eqeq1d.mm"
include "syl5ibrcom.mm"
include "necon3d.mm"
include "imp.mm"
include "sylan2.mm"
include "an4s.mm"
include "anassrs.mm"
include "pm3.2.mm"
include "syl5com.mm"
include "eldifsn.mm"
include "syl6ibr.mm"
include "imdistanda.mm"
include "ancom.mm"
include "3imtr4g.mm"
include "reximdv2.mm"
include "impbid2.mm"
include "ralbidva.mm"
include "pm5.32da.mm"
include "pm5.32i.mm"
include "bitri.mm"

theorem isdrngo3
  let vx: setvar x
  let vy: setvar y
  let cR: class R
  let cU: class U
  let cG: class G
  let cH: class H
  let cX: class X
  let cZ: class Z
  let vg: setvar g
  let vh: setvar h
  let vu: setvar u
  let vv: setvar v
  let vw: setvar w
  let vz: setvar z
  assume isdivrng1.1: |- G = ( 1st ` R )
  assume isdivrng1.2: |- H = ( 2nd ` R )
  assume isdivrng1.3: |- Z = ( GId ` G )
  assume isdivrng1.4: |- X = ran G
  assume isdivrng2.5: |- U = ( GId ` H )

  disjoint H x
  disjoint H y
  disjoint x y
  disjoint X x
  disjoint X y
  disjoint Z x
  disjoint Z y
  disjoint R x
  disjoint R y
  disjoint U x
  disjoint U y
  disjoint g h
  disjoint H u
  disjoint H v
  disjoint H w
  disjoint H z
  disjoint u x
  disjoint v x
  disjoint w x
  disjoint x z
  disjoint u y
  disjoint v y
  disjoint w y
  disjoint y z
  disjoint u v
  disjoint u w
  disjoint u z
  disjoint v w
  disjoint v z
  disjoint w z
  disjoint X u
  disjoint X v
  disjoint X w
  disjoint X z
  disjoint Z u
  disjoint Z v
  disjoint Z w
  disjoint Z z
  disjoint R u
  disjoint R v
  disjoint R w
  disjoint R z
  disjoint U u
  disjoint U v
  disjoint U w
  disjoint U z
  assert |- ( R e. DivRingOps <-> ( R e. RingOps /\ ( U =/= Z /\ A. x e. ( X \ { Z } ) E. y e. X ( y H x ) = U ) ) )

  proof
    cR
    cdrng
    wcel
    cR
    crngo
    wcel
    #
    cU
    cZ
    wne
    #
    vy
    cv
    #
    vx
    cv
    #
    cH
    co
    #
    cU
    wceq
    #
    vy
    cX
    cZ
    csn
    #
    cdif
    #
    wrex
    #
    vx
    @7
    wral
    #
    wa
    #
    wa
    @0
    @1
    @5
    vy
    cX
    wrex
    #
    vx
    @7
    wral
    #
    wa
    #
    wa
    vx
    vy
    cR
    cU
    cG
    cH
    cX
    cZ
    isdivrng1.1
    isdivrng1.2
    isdivrng1.3
    isdivrng1.4
    isdivrng2.5
    isdrngo2
    @0
    @10
    @13
    @0
    @1
    @9
    @12
    @0
    @1
    wa
    #
    @8
    @11
    vx
    @7
    @3
    @7
    wcel
    @14
    @3
    cX
    wcel
    #
    @8
    @11
    wb
    @3
    cX
    @6
    eldifi
    @14
    @15
    wa
    #
    @8
    @11
    @7
    cX
    wss
    @8
    @11
    wi
    cX
    @6
    difss
    @5
    vy
    @7
    cX
    ssrexv
    ax-mp
    @16
    @5
    @5
    vy
    cX
    @7
    @16
    @5
    @2
    cX
    wcel
    #
    wa
    @5
    @2
    @7
    wcel
    #
    wa
    @17
    @5
    wa
    @18
    @5
    wa
    @16
    @5
    @17
    @18
    @16
    @5
    wa
    #
    @17
    @17
    @2
    cZ
    wne
    #
    wa
    #
    @18
    @19
    @20
    @17
    @21
    @14
    @15
    @5
    @20
    @0
    @15
    @1
    @5
    @20
    @1
    @5
    wa
    @0
    @15
    wa
    #
    @4
    cZ
    wne
    #
    @20
    @5
    @23
    @1
    @4
    cU
    cZ
    neeq1
    biimparc
    @22
    @23
    @20
    @22
    @2
    cZ
    @4
    cZ
    @22
    @4
    cZ
    wceq
    @2
    cZ
    wceq
    #
    cZ
    @3
    cH
    co
    #
    cZ
    wceq
    @3
    cR
    cG
    cH
    cX
    cZ
    isdivrng1.3
    isdivrng1.4
    isdivrng1.1
    isdivrng1.2
    rngolz
    @24
    @4
    @25
    cZ
    @2
    cZ
    @3
    cH
    oveq1
    eqeq1d
    syl5ibrcom
    necon3d
    imp
    sylan2
    an4s
    anassrs
    @17
    @20
    pm3.2
    syl5com
    @2
    cX
    cZ
    eldifsn
    syl6ibr
    imdistanda
    @17
    @5
    ancom
    @18
    @5
    ancom
    3imtr4g
    reximdv2
    impbid2
    sylan2
    ralbidva
    pm5.32da
    pm5.32i
    bitri
end
