include "chlt.mm"
include "wcel.mm"
include "wa.mm"
include "wss.mm"
include "c0.mm"
include "wne.mm"
include "cv.mm"
include "co.mm"
include "wceq.mm"
include "wrex.mm"
include "crab.mm"
include "a1i.mm"
include "wex.mm"
include "simprr.mm"
include "n0.mm"
include "sylib.mm"
include "clat.mm"
include "hllat.mm"
include "ad3antrrr.mm"
include "simplrl.mm"
include "simpr.mm"
include "sseldd.mm"
include "lhpbase.mm"
include "ad3antlr.mm"
include "latmcl.mm"
include "syl3anc.mm"
include "eqidd.mm"
include "weq.mm"
include "oveq1.mm"
include "eqeq2d.mm"
include "rspcev.mm"
include "syl2anc.mm"
include "ovex.mm"
include "eleq1.mm"
include "eqeq1.mm"
include "rexbidv.mm"
include "elrab.mm"
include "syl6bb.mm"
include "spcev.mm"
include "sylibr.mm"
include "exlimddv.mm"
include "eqnetrd.mm"

theorem dihglblem2aN
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
  assert |- ( ( ( K e. HL /\ W e. H ) /\ ( S C_ B /\ S =/= (/) ) ) -> T =/= (/) )

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
    wa
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
    c0
    cT
    @12
    wceq
    @6
    dihglblem.t
    a1i
    @6
    vz
    cv
    #
    cS
    wcel
    #
    @12
    c0
    wne
    #
    vz
    @6
    @4
    @14
    vz
    wex
    @2
    @3
    @4
    simprr
    vz
    cS
    n0
    sylib
    @6
    @14
    wa
    #
    vw
    cv
    #
    @12
    wcel
    #
    vw
    wex
    #
    @15
    @16
    @13
    cW
    c.an
    co
    #
    cB
    wcel
    #
    @20
    @9
    wceq
    #
    vv
    cS
    wrex
    #
    @19
    @16
    cK
    clat
    wcel
    #
    @13
    cB
    wcel
    cW
    cB
    wcel
    #
    @21
    @0
    @24
    @1
    @5
    @14
    cK
    hllat
    ad3antrrr
    @16
    cS
    cB
    @13
    @2
    @3
    @4
    @14
    simplrl
    @6
    @14
    simpr
    #
    sseldd
    @1
    @25
    @0
    @5
    @14
    cB
    cH
    cK
    cW
    dihglblem.b
    dihglblem.h
    lhpbase
    ad3antlr
    cB
    cK
    c.an
    @13
    cW
    dihglblem.b
    dihglblem.m
    latmcl
    syl3anc
    @16
    @14
    @20
    @20
    wceq
    #
    @23
    @26
    @16
    @20
    eqidd
    @22
    @27
    vv
    @13
    cS
    vv
    vz
    weq
    @9
    @20
    @20
    @8
    @13
    cW
    c.an
    oveq1
    eqeq2d
    rspcev
    syl2anc
    @18
    @21
    @23
    wa
    #
    vw
    @20
    @13
    cW
    c.an
    ovex
    @17
    @20
    wceq
    @18
    @20
    @12
    wcel
    @28
    @17
    @20
    @12
    eleq1
    @11
    @23
    vu
    @20
    cB
    @7
    @20
    wceq
    @10
    @22
    vv
    cS
    @7
    @20
    @9
    eqeq1
    rexbidv
    elrab
    syl6bb
    spcev
    syl2anc
    vw
    @12
    n0
    sylibr
    exlimddv
    eqnetrd
end
