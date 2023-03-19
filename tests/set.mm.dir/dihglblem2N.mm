include "chlt.mm"
include "wcel.mm"
include "wa.mm"
include "wss.mm"
include "cfv.mm"
include "wbr.mm"
include "w3a.mm"
include "cv.mm"
include "co.mm"
include "clat.mm"
include "simpl1l.mm"
include "hllat.mm"
include "syl.mm"
include "ccla.mm"
include "simp1l.mm"
include "hlclat.mm"
include "wceq.mm"
include "wrex.mm"
include "crab.mm"
include "ssrab2.mm"
include "eqsstri.mm"
include "clatglbcl.mm"
include "sylancl.mm"
include "adantr.mm"
include "simpl2.mm"
include "simpr.mm"
include "sseldd.mm"
include "simpl1r.mm"
include "lhpbase.mm"
include "latmcl.mm"
include "syl3anc.mm"
include "eqidd.mm"
include "weq.mm"
include "oveq1.mm"
include "eqeq2d.mm"
include "rspcev.mm"
include "syl2anc.mm"
include "eqeq1.mm"
include "rexbidv.mm"
include "elrab.mm"
include "sylanbrc.mm"
include "syl6eleqr.mm"
include "clatglble.mm"
include "mp3an2.mm"
include "latmle1.mm"
include "lattrd.mm"
include "wral.mm"
include "cbvrexv.mm"
include "syl6bb.mm"
include "elrab2.mm"
include "wi.mm"
include "simp3.mm"
include "simp13.mm"
include "breq2.mm"
include "rspcva.mm"
include "simp11l.mm"
include "3ad2ant1.mm"
include "simp12.mm"
include "simp112.mm"
include "simp11r.mm"
include "wb.mm"
include "clatleglb.mm"
include "mpbird.mm"
include "simp113.mm"
include "latlem12.mm"
include "syl13anc.mm"
include "mpbi2and.mm"
include "3expia.mm"
include "biimprcd.mm"
include "syl6.mm"
include "rexlimdv.mm"
include "expimpd.mm"
include "syl5bi.mm"
include "ralrimiv.mm"
include "simp2.mm"
include "mp3an3.mm"
include "isglbd.mm"

theorem dihglblem2N
  let vv: setvar v
  let vu: setvar u
  let cB: class B
  let cS: class S
  let cT: class T
  let cG: class G
  let cH: class H
  let cK: class K
  let c.le: class .<_
  let c.an: class ./\
  let cW: class W
  let vx: setvar x
  let vy: setvar y
  let vw: setvar w
  let vz: setvar z
  assume dihglblem.b: |- B = ( Base ` K )
  assume dihglblem.l: |- .<_ = ( le ` K )
  assume dihglblem.m: |- ./\ = ( meet ` K )
  assume dihglblem.g: |- G = ( glb ` K )
  assume dihglblem.h: |- H = ( LHyp ` K )
  assume dihglblem.t: |- T = { u e. B | E. v e. S u = ( v ./\ W ) }

  disjoint u v
  disjoint ./\ u
  disjoint ./\ v
  disjoint B u
  disjoint S u
  disjoint S v
  disjoint W u
  disjoint W v
  disjoint x y
  disjoint w x
  disjoint u x
  disjoint v x
  disjoint x z
  disjoint ./\ x
  disjoint w y
  disjoint u y
  disjoint v y
  disjoint y z
  disjoint ./\ y
  disjoint u w
  disjoint v w
  disjoint w z
  disjoint ./\ w
  disjoint u z
  disjoint v z
  disjoint ./\ z
  disjoint .<_ x
  disjoint .<_ y
  disjoint .<_ w
  disjoint .<_ z
  disjoint B x
  disjoint B y
  disjoint B w
  disjoint B z
  disjoint G x
  disjoint G y
  disjoint G w
  disjoint G z
  disjoint H x
  disjoint H y
  disjoint H w
  disjoint H z
  disjoint K x
  disjoint K y
  disjoint K w
  disjoint K z
  disjoint S x
  disjoint S y
  disjoint S w
  disjoint S z
  disjoint T x
  disjoint T y
  disjoint T w
  disjoint T z
  disjoint W x
  disjoint W y
  disjoint W w
  disjoint W z
  assert |- ( ( ( K e. HL /\ W e. H ) /\ S C_ B /\ ( G ` S ) .<_ W ) -> ( G ` S ) = ( G ` T ) )

  proof
    cK
    chlt
    wcel
    #
    cW
    cH
    wcel
    #
    wa
    #
    cS
    cB
    wss
    #
    cS
    cG
    cfv
    #
    cW
    c.le
    wbr
    #
    w3a
    #
    vz
    vx
    cB
    cS
    cG
    cT
    cG
    cfv
    #
    cK
    c.le
    dihglblem.b
    dihglblem.l
    dihglblem.g
    @6
    vx
    cv
    #
    cS
    wcel
    #
    wa
    #
    cB
    cK
    c.le
    @7
    @8
    cW
    c.an
    co
    #
    @8
    dihglblem.b
    dihglblem.l
    @10
    @0
    cK
    clat
    wcel
    #
    @0
    @1
    @3
    @5
    @9
    simpl1l
    #
    cK
    hllat
    #
    syl
    #
    @6
    @7
    cB
    wcel
    #
    @9
    @6
    cK
    ccla
    wcel
    #
    cT
    cB
    wss
    #
    @16
    @6
    @0
    @17
    @0
    @1
    @3
    @5
    simp1l
    cK
    hlclat
    #
    syl
    #
    cT
    vu
    cv
    #
    vv
    cv
    #
    cW
    c.an
    co
    #
    wceq
    #
    vv
    cS
    wrex
    #
    vu
    cB
    crab
    #
    cB
    dihglblem.t
    @25
    vu
    cB
    ssrab2
    eqsstri
    #
    cB
    cT
    cG
    cK
    dihglblem.b
    dihglblem.g
    clatglbcl
    sylancl
    #
    adantr
    @10
    @12
    @8
    cB
    wcel
    #
    cW
    cB
    wcel
    #
    @11
    cB
    wcel
    #
    @15
    @10
    cS
    cB
    @8
    @2
    @3
    @5
    @9
    simpl2
    @6
    @9
    simpr
    #
    sseldd
    #
    @10
    @1
    @30
    @0
    @1
    @3
    @5
    @9
    simpl1r
    cB
    cH
    cK
    cW
    dihglblem.b
    dihglblem.h
    lhpbase
    #
    syl
    #
    cB
    cK
    c.an
    @8
    cW
    dihglblem.b
    dihglblem.m
    latmcl
    syl3anc
    #
    @33
    @10
    @17
    @11
    cT
    wcel
    #
    @7
    @11
    c.le
    wbr
    #
    @10
    @0
    @17
    @13
    @19
    syl
    @10
    @11
    @26
    cT
    @10
    @31
    @11
    @23
    wceq
    #
    vv
    cS
    wrex
    #
    @11
    @26
    wcel
    @36
    @10
    @9
    @11
    @11
    wceq
    #
    @40
    @32
    @10
    @11
    eqidd
    @39
    @41
    vv
    @8
    cS
    vv
    vx
    weq
    @23
    @11
    @11
    @22
    @8
    cW
    c.an
    oveq1
    eqeq2d
    rspcev
    syl2anc
    @25
    @40
    vu
    @11
    cB
    @21
    @11
    wceq
    @24
    @39
    vv
    cS
    @21
    @11
    @23
    eqeq1
    rexbidv
    elrab
    sylanbrc
    dihglblem.t
    syl6eleqr
    @17
    @18
    @37
    @38
    @27
    cB
    cT
    cG
    cK
    c.le
    @11
    dihglblem.b
    dihglblem.l
    dihglblem.g
    clatglble
    mp3an2
    syl2anc
    @10
    @12
    @29
    @30
    @11
    @8
    c.le
    wbr
    @15
    @33
    @35
    cB
    cK
    c.le
    c.an
    @8
    cW
    dihglblem.b
    dihglblem.l
    dihglblem.m
    latmle1
    syl3anc
    lattrd
    @6
    vz
    cv
    #
    cB
    wcel
    #
    @42
    @8
    c.le
    wbr
    #
    vx
    cS
    wral
    #
    w3a
    #
    @42
    @7
    c.le
    wbr
    #
    @42
    vw
    cv
    #
    c.le
    wbr
    #
    vw
    cT
    wral
    #
    @46
    @49
    vw
    cT
    @48
    cT
    wcel
    @48
    cB
    wcel
    #
    @48
    vy
    cv
    #
    cW
    c.an
    co
    #
    wceq
    #
    vy
    cS
    wrex
    #
    wa
    @46
    @49
    @25
    @55
    vu
    @48
    cB
    cT
    vu
    vw
    weq
    #
    @25
    @48
    @23
    wceq
    #
    vv
    cS
    wrex
    @55
    @56
    @24
    @57
    vv
    cS
    @21
    @48
    @23
    eqeq1
    rexbidv
    @57
    @54
    vv
    vy
    cS
    vv
    vy
    weq
    @23
    @53
    @48
    @22
    @52
    cW
    c.an
    oveq1
    eqeq2d
    cbvrexv
    syl6bb
    dihglblem.t
    elrab2
    @46
    @51
    @55
    @49
    @46
    @51
    wa
    #
    @54
    @49
    vy
    cS
    @58
    @52
    cS
    wcel
    #
    @42
    @53
    c.le
    wbr
    #
    @54
    @49
    wi
    @46
    @51
    @59
    @60
    @46
    @51
    @59
    w3a
    #
    @42
    @52
    c.le
    wbr
    #
    @42
    cW
    c.le
    wbr
    #
    @60
    @61
    @59
    @45
    @62
    @46
    @51
    @59
    simp3
    #
    @6
    @43
    @45
    @51
    @59
    simp13
    #
    @44
    @62
    vx
    @52
    cS
    @8
    @52
    @42
    c.le
    breq2
    rspcva
    syl2anc
    @61
    cB
    cK
    c.le
    @42
    @4
    cW
    dihglblem.b
    dihglblem.l
    @61
    @0
    @12
    @46
    @51
    @0
    @59
    @0
    @1
    @3
    @5
    @43
    @45
    simp11l
    #
    3ad2ant1
    #
    @14
    syl
    #
    @6
    @43
    @45
    @51
    @59
    simp12
    #
    @61
    @17
    @3
    @4
    cB
    wcel
    @61
    @0
    @17
    @67
    @19
    syl
    #
    @2
    @3
    @5
    @43
    @45
    @51
    @59
    simp112
    #
    cB
    cS
    cG
    cK
    dihglblem.b
    dihglblem.g
    clatglbcl
    syl2anc
    @61
    @1
    @30
    @46
    @51
    @1
    @59
    @0
    @1
    @3
    @5
    @43
    @45
    simp11r
    3ad2ant1
    @34
    syl
    #
    @61
    @42
    @4
    c.le
    wbr
    #
    @45
    @65
    @61
    @17
    @43
    @3
    @73
    @45
    wb
    @70
    @69
    @71
    vx
    cB
    cS
    cG
    cK
    c.le
    @42
    dihglblem.b
    dihglblem.l
    dihglblem.g
    clatleglb
    syl3anc
    mpbird
    @2
    @3
    @5
    @43
    @45
    @51
    @59
    simp113
    lattrd
    @61
    @12
    @43
    @52
    cB
    wcel
    @30
    @62
    @63
    wa
    @60
    wb
    @68
    @69
    @61
    cS
    cB
    @52
    @71
    @64
    sseldd
    @72
    cB
    cK
    c.le
    c.an
    @42
    @52
    cW
    dihglblem.b
    dihglblem.l
    dihglblem.m
    latlem12
    syl13anc
    mpbi2and
    3expia
    @54
    @49
    @60
    @48
    @53
    @42
    c.le
    breq2
    biimprcd
    syl6
    rexlimdv
    expimpd
    syl5bi
    ralrimiv
    @46
    @17
    @43
    @47
    @50
    wb
    #
    @46
    @0
    @17
    @66
    @19
    syl
    @6
    @43
    @45
    simp2
    @17
    @43
    @18
    @74
    @27
    vw
    cB
    cT
    cG
    cK
    c.le
    @42
    dihglblem.b
    dihglblem.l
    dihglblem.g
    clatleglb
    mp3an3
    syl2anc
    mpbird
    @20
    @2
    @3
    @5
    simp2
    @28
    isglbd
end
