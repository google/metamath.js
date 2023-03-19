include "wcel.mm"
include "wa.mm"
include "cv.mm"
include "wbr.mm"
include "crab.mm"
include "wfn.mm"
include "ctrl.mm"
include "cfv.mm"
include "cltrn.mm"
include "cmpt.mm"
include "fvex.mm"
include "rabex.mm"
include "eqid.mm"
include "fnmpti.mm"
include "diafval.mm"
include "fneq1d.mm"
include "mpbiri.mm"

theorem diafn
  let vx: setvar x
  let cB: class B
  let cH: class H
  let cI: class I
  let cK: class K
  let c.le: class .<_
  let cV: class V
  let cW: class W
  let vy: setvar y
  let vf: setvar f
  let cX: class X
  assume diafn.b: |- B = ( Base ` K )
  assume diafn.l: |- .<_ = ( le ` K )
  assume diafn.h: |- H = ( LHyp ` K )
  assume diafn.i: |- I = ( ( DIsoA ` K ) ` W )

  disjoint .<_ x
  disjoint B x
  disjoint K x
  disjoint W x
  disjoint x y
  disjoint .<_ y
  disjoint B y
  disjoint f x
  disjoint f y
  disjoint K f
  disjoint K y
  disjoint W f
  disjoint W y
  disjoint X x
  assert |- ( ( K e. V /\ W e. H ) -> I Fn { x e. B | x .<_ W } )

  proof
    cK
    cV
    wcel
    cW
    cH
    wcel
    wa
    #
    cI
    vx
    cv
    cW
    c.le
    wbr
    vx
    cB
    crab
    #
    wfn
    vy
    @1
    vf
    cv
    cW
    cK
    ctrl
    cfv
    cfv
    #
    cfv
    vy
    cv
    c.le
    wbr
    #
    vf
    cW
    cK
    cltrn
    cfv
    #
    cfv
    #
    crab
    #
    cmpt
    #
    @1
    wfn
    vy
    @1
    @6
    @7
    @3
    vf
    @5
    cW
    @4
    fvex
    rabex
    @7
    eqid
    fnmpti
    @0
    @1
    cI
    @7
    vy
    vx
    cB
    @2
    @5
    vf
    cH
    cI
    cK
    c.le
    cV
    cW
    diafn.b
    diafn.l
    diafn.h
    @5
    eqid
    @2
    eqid
    diafn.i
    diafval
    fneq1d
    mpbiri
end
