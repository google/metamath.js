include "chlt.mm"
include "wcel.mm"
include "wa.mm"
include "wss.mm"
include "c0.mm"
include "wne.mm"
include "cfv.mm"
include "wbr.mm"
include "w3a.mm"
include "cv.mm"
include "ciin.mm"
include "cdm.mm"
include "wceq.mm"
include "simp1.mm"
include "crab.mm"
include "co.mm"
include "wrex.mm"
include "wi.mm"
include "clat.mm"
include "simp11l.mm"
include "hllat.mm"
include "syl.mm"
include "simp12l.mm"
include "simp3.mm"
include "sseldd.mm"
include "simp11r.mm"
include "lhpbase.mm"
include "latmle2.mm"
include "syl3anc.mm"
include "3expia.mm"
include "breq1.mm"
include "biimprcd.mm"
include "syl6.mm"
include "rexlimdv.mm"
include "ss2rabdv.mm"
include "syl5eqss.mm"
include "dibdmN.mm"
include "3ad2ant1.mm"
include "sseqtr4d.mm"
include "dihglblem2aN.mm"
include "3adant3.mm"
include "dibglbN.mm"
include "syl12anc.mm"
include "dihglblem2N.mm"
include "3adant2r.mm"
include "fveq2d.mm"
include "simpl1.mm"
include "sselda.mm"
include "elrab.mm"
include "sylib.mm"
include "dihvalb.mm"
include "syl2anc.mm"
include "iineq2dv.mm"
include "3eqtr4rd.mm"
include "ccla.mm"
include "simp1l.mm"
include "hlclat.mm"
include "simp2l.mm"
include "clatglbcl.mm"
include "3eqtr2rd.mm"

theorem dihglblem3N
  let vx: setvar x
  let vv: setvar v
  let vu: setvar u
  let cB: class B
  let cS: class S
  let cT: class T
  let cG: class G
  let cH: class H
  let cI: class I
  let cJ: class J
  let cK: class K
  let c.le: class .<_
  let c.an: class ./\
  let cW: class W
  let vy: setvar y
  let vw: setvar w
  let vz: setvar z
  assume dihglblem.b: |- B = ( Base ` K )
  assume dihglblem.l: |- .<_ = ( le ` K )
  assume dihglblem.m: |- ./\ = ( meet ` K )
  assume dihglblem.g: |- G = ( glb ` K )
  assume dihglblem.h: |- H = ( LHyp ` K )
  assume dihglblem.t: |- T = { u e. B | E. v e. S u = ( v ./\ W ) }
  assume dihglblem.i: |- J = ( ( DIsoB ` K ) ` W )
  assume dihglblem.ih: |- I = ( ( DIsoH ` K ) ` W )

  disjoint u x
  disjoint v x
  disjoint ./\ x
  disjoint u v
  disjoint ./\ u
  disjoint ./\ v
  disjoint .<_ x
  disjoint B x
  disjoint B u
  disjoint G x
  disjoint H x
  disjoint K x
  disjoint S x
  disjoint S u
  disjoint S v
  disjoint T x
  disjoint W x
  disjoint W u
  disjoint W v
  disjoint .<_ u
  disjoint .<_ v
  disjoint B v
  disjoint G u
  disjoint G v
  disjoint H u
  disjoint H v
  disjoint K u
  disjoint K v
  disjoint x y
  disjoint w x
  disjoint x z
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
  disjoint .<_ y
  disjoint .<_ w
  disjoint .<_ z
  disjoint B y
  disjoint B w
  disjoint B z
  disjoint G y
  disjoint G w
  disjoint G z
  disjoint H y
  disjoint H w
  disjoint H z
  disjoint K y
  disjoint K w
  disjoint K z
  disjoint S y
  disjoint S w
  disjoint S z
  disjoint T y
  disjoint T w
  disjoint T z
  disjoint W y
  disjoint W w
  disjoint W z
  assert |- ( ( ( K e. HL /\ W e. H ) /\ ( S C_ B /\ S =/= (/) ) /\ ( G ` S ) .<_ W ) -> ( I ` ( G ` T ) ) = |^|_ x e. T ( I ` x ) )

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
    c0
    wne
    #
    wa
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
    vx
    cT
    vx
    cv
    #
    cI
    cfv
    #
    ciin
    #
    @6
    cJ
    cfv
    #
    @6
    cI
    cfv
    #
    cT
    cG
    cfv
    #
    cI
    cfv
    @8
    @14
    cJ
    cfv
    #
    vx
    cT
    @9
    cJ
    cfv
    #
    ciin
    #
    @12
    @11
    @8
    @2
    cT
    cJ
    cdm
    #
    wss
    cT
    c0
    wne
    #
    @15
    @17
    wceq
    @2
    @5
    @7
    simp1
    #
    @8
    cT
    vu
    cv
    #
    cW
    c.le
    wbr
    #
    vu
    cB
    crab
    #
    @18
    @8
    cT
    @21
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
    @23
    dihglblem.t
    @8
    @27
    @22
    vu
    cB
    @8
    @21
    cB
    wcel
    #
    wa
    #
    @26
    @22
    vv
    cS
    @29
    @24
    cS
    wcel
    #
    @25
    cW
    c.le
    wbr
    #
    @26
    @22
    wi
    @8
    @28
    @30
    @31
    @8
    @28
    @30
    w3a
    #
    cK
    clat
    wcel
    #
    @24
    cB
    wcel
    cW
    cB
    wcel
    #
    @31
    @32
    @0
    @33
    @0
    @1
    @5
    @7
    @28
    @30
    simp11l
    cK
    hllat
    syl
    @32
    cS
    cB
    @24
    @3
    @4
    @2
    @7
    @28
    @30
    simp12l
    @8
    @28
    @30
    simp3
    sseldd
    @32
    @1
    @34
    @0
    @1
    @5
    @7
    @28
    @30
    simp11r
    cB
    cH
    cK
    cW
    dihglblem.b
    dihglblem.h
    lhpbase
    syl
    cB
    cK
    c.le
    c.an
    @24
    cW
    dihglblem.b
    dihglblem.l
    dihglblem.m
    latmle2
    syl3anc
    3expia
    @26
    @22
    @31
    @21
    @25
    cW
    c.le
    breq1
    biimprcd
    syl6
    rexlimdv
    ss2rabdv
    syl5eqss
    #
    @2
    @5
    @18
    @23
    wceq
    @7
    vu
    cB
    cH
    cJ
    cK
    c.le
    chlt
    cW
    dihglblem.b
    dihglblem.l
    dihglblem.h
    dihglblem.i
    dibdmN
    3ad2ant1
    sseqtr4d
    @2
    @5
    @19
    @7
    vv
    vu
    cB
    cS
    cT
    cG
    cH
    cK
    c.le
    c.an
    cW
    dihglblem.b
    dihglblem.l
    dihglblem.m
    dihglblem.g
    dihglblem.h
    dihglblem.t
    dihglblem2aN
    3adant3
    vx
    cT
    cG
    cH
    cJ
    cK
    cW
    dihglblem.g
    dihglblem.h
    dihglblem.i
    dibglbN
    syl12anc
    @8
    @6
    @14
    cJ
    @2
    @3
    @7
    @6
    @14
    wceq
    @4
    vv
    vu
    cB
    cS
    cT
    cG
    cH
    cK
    c.le
    c.an
    cW
    dihglblem.b
    dihglblem.l
    dihglblem.m
    dihglblem.g
    dihglblem.h
    dihglblem.t
    dihglblem2N
    3adant2r
    #
    fveq2d
    @8
    vx
    cT
    @10
    @16
    @8
    @9
    cT
    wcel
    #
    wa
    #
    @2
    @9
    cB
    wcel
    @9
    cW
    c.le
    wbr
    #
    wa
    #
    @10
    @16
    wceq
    @2
    @5
    @7
    @37
    simpl1
    @38
    @9
    @23
    wcel
    @40
    @8
    cT
    @23
    @9
    @35
    sselda
    @22
    @39
    vu
    @9
    cB
    @21
    @9
    cW
    c.le
    breq1
    elrab
    sylib
    cB
    cJ
    cH
    cI
    cK
    c.le
    chlt
    cW
    @9
    dihglblem.b
    dihglblem.l
    dihglblem.h
    dihglblem.ih
    dihglblem.i
    dihvalb
    syl2anc
    iineq2dv
    3eqtr4rd
    @8
    @2
    @6
    cB
    wcel
    #
    @7
    @13
    @12
    wceq
    @20
    @8
    cK
    ccla
    wcel
    #
    @3
    @41
    @8
    @0
    @42
    @0
    @1
    @5
    @7
    simp1l
    cK
    hlclat
    syl
    @2
    @3
    @4
    @7
    simp2l
    cB
    cS
    cG
    cK
    dihglblem.b
    dihglblem.g
    clatglbcl
    syl2anc
    @2
    @5
    @7
    simp3
    cB
    cJ
    cH
    cI
    cK
    c.le
    chlt
    cW
    @6
    dihglblem.b
    dihglblem.l
    dihglblem.h
    dihglblem.ih
    dihglblem.i
    dihvalb
    syl12anc
    @8
    @6
    @14
    cI
    @36
    fveq2d
    3eqtr2rd
end
