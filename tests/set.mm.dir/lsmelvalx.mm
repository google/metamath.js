include "wcel.mm"
include "wss.mm"
include "w3a.mm"
include "co.mm"
include "cv.mm"
include "cmpt2.mm"
include "crn.mm"
include "wceq.mm"
include "wrex.mm"
include "lsmvalx.mm"
include "eleq2d.mm"
include "eqid.mm"
include "ovex.mm"
include "elrnmpt2.mm"
include "syl6bb.mm"

theorem lsmelvalx
  let vy: setvar y
  let vz: setvar z
  let cB: class B
  let c.pl: class .+
  let c.po: class .(+)
  let cT: class T
  let cU: class U
  let cG: class G
  let cV: class V
  let cX: class X
  let vt: setvar t
  let vu: setvar u
  let vw: setvar w
  let vx: setvar x
  let cY: class Y
  assume lsmfval.v: |- B = ( Base ` G )
  assume lsmfval.a: |- .+ = ( +g ` G )
  assume lsmfval.s: |- .(+) = ( LSSum ` G )

  disjoint y z
  disjoint .+ y
  disjoint .+ z
  disjoint B y
  disjoint B z
  disjoint T y
  disjoint T z
  disjoint X y
  disjoint X z
  disjoint G y
  disjoint G z
  disjoint U y
  disjoint U z
  disjoint t u
  disjoint t w
  disjoint t x
  disjoint t y
  disjoint t z
  disjoint .+ t
  disjoint u w
  disjoint u x
  disjoint u y
  disjoint u z
  disjoint .+ u
  disjoint w x
  disjoint w y
  disjoint w z
  disjoint .+ w
  disjoint x y
  disjoint x z
  disjoint .+ x
  disjoint B t
  disjoint B u
  disjoint B w
  disjoint B x
  disjoint T t
  disjoint T u
  disjoint T x
  disjoint X x
  disjoint G t
  disjoint G u
  disjoint G w
  disjoint G x
  disjoint U t
  disjoint U u
  disjoint U x
  disjoint Y x
  disjoint Y y
  assert |- ( ( G e. V /\ T C_ B /\ U C_ B ) -> ( X e. ( T .(+) U ) <-> E. y e. T E. z e. U X = ( y .+ z ) ) )

  proof
    cG
    cV
    wcel
    cT
    cB
    wss
    cU
    cB
    wss
    w3a
    #
    cX
    cT
    cU
    c.po
    co
    #
    wcel
    cX
    vy
    vz
    cT
    cU
    vy
    cv
    #
    vz
    cv
    #
    c.pl
    co
    #
    cmpt2
    #
    crn
    #
    wcel
    cX
    @4
    wceq
    vz
    cU
    wrex
    vy
    cT
    wrex
    @0
    @1
    @6
    cX
    vy
    vz
    cB
    c.pl
    c.po
    cT
    cU
    cG
    cV
    lsmfval.v
    lsmfval.a
    lsmfval.s
    lsmvalx
    eleq2d
    vy
    vz
    cT
    cU
    @4
    cX
    @5
    @5
    eqid
    @2
    @3
    c.pl
    ovex
    elrnmpt2
    syl6bb
end
