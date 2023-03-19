include "chlt.mm"
include "wcel.mm"
include "wa.mm"
include "w3a.mm"
include "cop.mm"
include "co.mm"
include "cv.mm"
include "wceq.mm"
include "wrex.mm"
include "wex.mm"
include "csubg.mm"
include "cfv.mm"
include "wb.mm"
include "clmod.mm"
include "wss.mm"
include "id.mm"
include "dvhlmod.mm"
include "3ad2ant1.mm"
include "lsssssubg.mm"
include "syl.mm"
include "simp2.mm"
include "sseldd.mm"
include "simp3.mm"
include "lsmelval.mm"
include "syl2anc.mm"
include "wrel.mm"
include "cltrn.mm"
include "ctendo.mm"
include "cxp.mm"
include "cbs.mm"
include "eqid.mm"
include "lssss.mm"
include "3ad2ant3.mm"
include "dvhvbase.mm"
include "sseqtrd.mm"
include "relxp.mm"
include "relss.mm"
include "mpisyl.mm"
include "oveq2.mm"
include "eqeq2d.mm"
include "exopxfr2.mm"
include "rexbidv.mm"
include "3ad2ant2.mm"
include "oveq1.mm"
include "anbi2d.mm"
include "2exbidv.mm"
include "19.42vv.mm"
include "anass.mm"
include "2exbii.mm"
include "bicomi.mm"
include "a1i.mm"
include "syl5bbr.mm"
include "bitrd.mm"
include "3bitrd.mm"

theorem dvhopellsm
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let vw: setvar w
  let c.pl: class .+
  let c.po: class .(+)
  let cS: class S
  let cT: class T
  let cU: class U
  let cF: class F
  let cH: class H
  let cK: class K
  let cW: class W
  let cX: class X
  let cY: class Y
  let vu: setvar u
  let vv: setvar v
  assume dvhopellsm.h: |- H = ( LHyp ` K )
  assume dvhopellsm.u: |- U = ( ( DVecH ` K ) ` W )
  assume dvhopellsm.a: |- .+ = ( +g ` U )
  assume dvhopellsm.s: |- S = ( LSubSp ` U )
  assume dvhopellsm.p: |- .(+) = ( LSSum ` U )

  disjoint w x
  disjoint w y
  disjoint w z
  disjoint .+ w
  disjoint x y
  disjoint x z
  disjoint .+ x
  disjoint y z
  disjoint .+ y
  disjoint .+ z
  disjoint F w
  disjoint F x
  disjoint F y
  disjoint F z
  disjoint H x
  disjoint H y
  disjoint K x
  disjoint K y
  disjoint S x
  disjoint S y
  disjoint T w
  disjoint T x
  disjoint T y
  disjoint T z
  disjoint W x
  disjoint W y
  disjoint X w
  disjoint X x
  disjoint X y
  disjoint X z
  disjoint Y w
  disjoint Y x
  disjoint Y y
  disjoint Y z
  disjoint u v
  disjoint u w
  disjoint u x
  disjoint u y
  disjoint u z
  disjoint .+ u
  disjoint v w
  disjoint v x
  disjoint v y
  disjoint v z
  disjoint .+ v
  disjoint F u
  disjoint F v
  disjoint H u
  disjoint K u
  disjoint S u
  disjoint T u
  disjoint T v
  disjoint U u
  disjoint U v
  disjoint W u
  disjoint X u
  disjoint X v
  disjoint Y u
  disjoint Y v
  assert |- ( ( ( K e. HL /\ W e. H ) /\ X e. S /\ Y e. S ) -> ( <. F , T >. e. ( X .(+) Y ) <-> E. x E. y E. z E. w ( ( <. x , y >. e. X /\ <. z , w >. e. Y ) /\ <. F , T >. = ( <. x , y >. .+ <. z , w >. ) ) ) )

  proof
    cK
    chlt
    wcel
    cW
    cH
    wcel
    wa
    #
    cX
    cS
    wcel
    #
    cY
    cS
    wcel
    #
    w3a
    #
    cF
    cT
    cop
    #
    cX
    cY
    c.po
    co
    wcel
    #
    @4
    vu
    cv
    #
    vv
    cv
    #
    c.pl
    co
    #
    wceq
    #
    vv
    cY
    wrex
    #
    vu
    cX
    wrex
    #
    vz
    cv
    vw
    cv
    cop
    #
    cY
    wcel
    #
    @4
    @6
    @12
    c.pl
    co
    #
    wceq
    #
    wa
    #
    vw
    wex
    vz
    wex
    #
    vu
    cX
    wrex
    #
    vx
    cv
    vy
    cv
    cop
    #
    cX
    wcel
    #
    @13
    wa
    @4
    @19
    @12
    c.pl
    co
    #
    wceq
    #
    wa
    #
    vw
    wex
    vz
    wex
    #
    vy
    wex
    vx
    wex
    #
    @3
    cX
    cU
    csubg
    cfv
    #
    wcel
    cY
    @26
    wcel
    @5
    @11
    wb
    @3
    cS
    @26
    cX
    @3
    cU
    clmod
    wcel
    #
    cS
    @26
    wss
    @0
    @1
    @27
    @2
    @0
    cU
    cH
    cK
    cW
    dvhopellsm.h
    dvhopellsm.u
    @0
    id
    dvhlmod
    3ad2ant1
    cS
    cU
    dvhopellsm.s
    lsssssubg
    syl
    #
    @0
    @1
    @2
    simp2
    sseldd
    @3
    cS
    @26
    cY
    @28
    @0
    @1
    @2
    simp3
    sseldd
    vu
    vv
    c.pl
    c.po
    cX
    cY
    cU
    @4
    dvhopellsm.a
    dvhopellsm.p
    lsmelval
    syl2anc
    @3
    @10
    @17
    vu
    cX
    @3
    cY
    wrel
    #
    @10
    @17
    wb
    @3
    cY
    cW
    cK
    cltrn
    cfv
    cfv
    #
    cW
    cK
    ctendo
    cfv
    cfv
    #
    cxp
    #
    wss
    @32
    wrel
    #
    @29
    @3
    cY
    cU
    cbs
    cfv
    #
    @32
    @2
    @0
    cY
    @34
    wss
    @1
    cS
    cY
    @34
    cU
    @34
    eqid
    #
    dvhopellsm.s
    lssss
    3ad2ant3
    @0
    @1
    @34
    @32
    wceq
    @2
    @30
    cU
    @31
    cH
    cK
    @34
    cW
    chlt
    dvhopellsm.h
    @30
    eqid
    @31
    eqid
    dvhopellsm.u
    @35
    dvhvbase
    3ad2ant1
    #
    sseqtrd
    @30
    @31
    relxp
    #
    cY
    @32
    relss
    mpisyl
    @9
    @15
    vv
    vz
    vw
    cY
    @7
    @12
    wceq
    @8
    @14
    @4
    @7
    @12
    @6
    c.pl
    oveq2
    eqeq2d
    exopxfr2
    syl
    rexbidv
    @3
    @18
    @20
    @13
    @22
    wa
    #
    vw
    wex
    vz
    wex
    #
    wa
    #
    vy
    wex
    vx
    wex
    #
    @25
    @3
    cX
    wrel
    #
    @18
    @41
    wb
    @3
    cX
    @32
    wss
    @33
    @42
    @3
    cX
    @34
    @32
    @1
    @0
    cX
    @34
    wss
    @2
    cS
    cX
    @34
    cU
    @35
    dvhopellsm.s
    lssss
    3ad2ant2
    @36
    sseqtrd
    @37
    cX
    @32
    relss
    mpisyl
    @17
    @39
    vu
    vx
    vy
    cX
    @6
    @19
    wceq
    #
    @16
    @38
    vz
    vw
    @43
    @15
    @22
    @13
    @43
    @14
    @21
    @4
    @6
    @19
    @12
    c.pl
    oveq1
    eqeq2d
    anbi2d
    2exbidv
    exopxfr2
    syl
    @3
    @40
    @24
    vx
    vy
    @40
    @20
    @38
    wa
    #
    vw
    wex
    vz
    wex
    #
    @3
    @24
    @20
    @38
    vz
    vw
    19.42vv
    @45
    @24
    wb
    @3
    @24
    @45
    @23
    @44
    vz
    vw
    @20
    @13
    @22
    anass
    2exbii
    bicomi
    a1i
    syl5bbr
    2exbidv
    bitrd
    3bitrd
end
