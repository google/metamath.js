include "chlt.mm"
include "wcel.mm"
include "wa.mm"
include "wss.mm"
include "c0.mm"
include "wne.mm"
include "cfv.mm"
include "cv.mm"
include "wral.mm"
include "ciin.mm"
include "wbr.mm"
include "ccla.mm"
include "hlclat.mm"
include "ad3antrrr.mm"
include "simplrl.mm"
include "simpr.mm"
include "clatglble.mm"
include "syl3anc.mm"
include "wb.mm"
include "simpll.mm"
include "clatglbcl.mm"
include "syl2anc.mm"
include "sseldd.mm"
include "dihord.mm"
include "mpbird.mm"
include "ralrimiva.mm"
include "ssiin.mm"
include "sylibr.mm"

theorem dihglblem4
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
  disjoint I x
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
  assert |- ( ( ( K e. HL /\ W e. H ) /\ ( S C_ B /\ S =/= (/) ) ) -> ( I ` ( G ` S ) ) C_ |^|_ x e. S ( I ` x ) )

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
    cS
    cG
    cfv
    #
    cI
    cfv
    #
    vx
    cv
    #
    cI
    cfv
    #
    wss
    #
    vx
    cS
    wral
    @8
    vx
    cS
    @10
    ciin
    wss
    @6
    @11
    vx
    cS
    @6
    @9
    cS
    wcel
    #
    wa
    #
    @11
    @7
    @9
    c.le
    wbr
    #
    @13
    cK
    ccla
    wcel
    #
    @3
    @12
    @14
    @0
    @15
    @1
    @5
    @12
    cK
    hlclat
    ad3antrrr
    #
    @2
    @3
    @4
    @12
    simplrl
    #
    @6
    @12
    simpr
    #
    cB
    cS
    cG
    cK
    c.le
    @9
    dihglblem.b
    dihglblem.l
    dihglblem.g
    clatglble
    syl3anc
    @13
    @2
    @7
    cB
    wcel
    #
    @9
    cB
    wcel
    @11
    @14
    wb
    @2
    @5
    @12
    simpll
    @13
    @15
    @3
    @19
    @16
    @17
    cB
    cS
    cG
    cK
    dihglblem.b
    dihglblem.g
    clatglbcl
    syl2anc
    @13
    cS
    cB
    @9
    @17
    @18
    sseldd
    cB
    cH
    cI
    cK
    c.le
    cW
    @7
    @9
    dihglblem.b
    dihglblem.l
    dihglblem.h
    dihglblem.ih
    dihord
    syl3anc
    mpbird
    ralrimiva
    vx
    cS
    @10
    @8
    ssiin
    sylibr
end
