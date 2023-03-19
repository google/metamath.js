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
include "wceq.mm"
include "dihglblem2N.mm"
include "3adant2r.mm"
include "fveq2d.mm"
include "dihglblem3N.mm"
include "eqtrd.mm"

theorem dihglblem3aN
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
  assert |- ( ( ( K e. HL /\ W e. H ) /\ ( S C_ B /\ S =/= (/) ) /\ ( G ` S ) .<_ W ) -> ( I ` ( G ` S ) ) = |^|_ x e. T ( I ` x ) )

  proof
    cK
    chlt
    wcel
    cW
    cH
    wcel
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
    @3
    cI
    cfv
    cT
    cG
    cfv
    #
    cI
    cfv
    vx
    cT
    vx
    cv
    cI
    cfv
    ciin
    @5
    @3
    @6
    cI
    @0
    @1
    @4
    @3
    @6
    wceq
    @2
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
    fveq2d
    vx
    vv
    vu
    cB
    cS
    cT
    cG
    cH
    cI
    cJ
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
    dihglblem.i
    dihglblem.ih
    dihglblem3N
    eqtrd
end
