include "cal.mm"
include "wcel.mm"
include "wne.mm"
include "cv.mm"
include "wbr.mm"
include "wrex.mm"
include "wi.mm"
include "wral.mm"
include "clat.mm"
include "cglb.mm"
include "cfv.mm"
include "cdm.mm"
include "eqid.mm"
include "isatl.mm"
include "simp3bi.mm"
include "wceq.mm"
include "neeq1.mm"
include "breq2.mm"
include "rexbidv.mm"
include "imbi12d.mm"
include "rspccv.mm"
include "syl.mm"
include "3imp.mm"

theorem atlex
  let vy: setvar y
  let cA: class A
  let cB: class B
  let cK: class K
  let c.le: class .<_
  let cX: class X
  let c.0: class .0.
  let vx: setvar x
  assume atlex.b: |- B = ( Base ` K )
  assume atlex.l: |- .<_ = ( le ` K )
  assume atlex.z: |- .0. = ( 0. ` K )
  assume atlex.a: |- A = ( Atoms ` K )

  disjoint A y
  disjoint K y
  disjoint X y
  disjoint x y
  disjoint A x
  disjoint B x
  disjoint K x
  disjoint .<_ x
  disjoint X x
  disjoint .0. x
  assert |- ( ( K e. AtLat /\ X e. B /\ X =/= .0. ) -> E. y e. A y .<_ X )

  proof
    cK
    cal
    wcel
    #
    cX
    cB
    wcel
    #
    cX
    c.0
    wne
    #
    vy
    cv
    #
    cX
    c.le
    wbr
    #
    vy
    cA
    wrex
    #
    @0
    vx
    cv
    #
    c.0
    wne
    #
    @3
    @6
    c.le
    wbr
    #
    vy
    cA
    wrex
    #
    wi
    #
    vx
    cB
    wral
    #
    @1
    @2
    @5
    wi
    #
    wi
    @0
    cK
    clat
    wcel
    cB
    cK
    cglb
    cfv
    #
    cdm
    wcel
    @11
    vx
    vy
    cA
    cB
    @13
    cK
    c.le
    c.0
    atlex.b
    @13
    eqid
    atlex.l
    atlex.z
    atlex.a
    isatl
    simp3bi
    @10
    @12
    vx
    cX
    cB
    @6
    cX
    wceq
    #
    @7
    @2
    @9
    @5
    @6
    cX
    c.0
    neeq1
    @14
    @8
    @4
    vy
    cA
    @6
    cX
    @3
    c.le
    breq2
    rexbidv
    imbi12d
    rspccv
    syl
    3imp
end
