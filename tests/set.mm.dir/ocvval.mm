include "wss.mm"
include "cpw.mm"
include "wcel.mm"
include "cfv.mm"
include "cv.mm"
include "co.mm"
include "wceq.mm"
include "wral.mm"
include "crab.mm"
include "cbs.mm"
include "cvv.mm"
include "fvex.mm"
include "eqeltri.mm"
include "elpw2.mm"
include "cmpt.mm"
include "ocvfval.mm"
include "fveq1d.mm"
include "raleq.mm"
include "rabbidv.mm"
include "eqid.mm"
include "rabex.mm"
include "fvmpt.mm"
include "sylan9eq.mm"
include "wn.mm"
include "c0.mm"
include "0fv.mm"
include "cocv.mm"
include "fvprc.mm"
include "syl5eq.mm"
include "ssrab2.mm"
include "sseq0.mm"
include "sylancr.mm"
include "3eqtr4a.mm"
include "adantr.mm"
include "pm2.61ian.mm"
include "sylbir.mm"

theorem ocvval
  let vx: setvar x
  let vy: setvar y
  let cS: class S
  let cF: class F
  let c.xi: class .,
  let c.pe: class ._|_
  let cV: class V
  let cW: class W
  let c.0: class .0.
  let vh: setvar h
  let vs: setvar s
  let cA: class A
  let cB: class B
  assume ocvfval.v: |- V = ( Base ` W )
  assume ocvfval.i: |- ., = ( .i ` W )
  assume ocvfval.f: |- F = ( Scalar ` W )
  assume ocvfval.z: |- .0. = ( 0g ` F )
  assume ocvfval.o: |- ._|_ = ( ocv ` W )

  disjoint x y
  disjoint .0. x
  disjoint .0. y
  disjoint V x
  disjoint V y
  disjoint W x
  disjoint W y
  disjoint ., x
  disjoint ., y
  disjoint S x
  disjoint S y
  disjoint h s
  disjoint h x
  disjoint h y
  disjoint .0. h
  disjoint s x
  disjoint s y
  disjoint .0. s
  disjoint A x
  disjoint A y
  disjoint B x
  disjoint V h
  disjoint V s
  disjoint W h
  disjoint W s
  disjoint ., h
  disjoint ., s
  disjoint S s
  assert |- ( S C_ V -> ( ._|_ ` S ) = { x e. V | A. y e. S ( x ., y ) = .0. } )

  proof
    cS
    cV
    wss
    cS
    cV
    cpw
    #
    wcel
    #
    cS
    c.pe
    cfv
    #
    vx
    cv
    vy
    cv
    c.xi
    co
    c.0
    wceq
    #
    vy
    cS
    wral
    #
    vx
    cV
    crab
    #
    wceq
    #
    cS
    cV
    cV
    cW
    cbs
    cfv
    #
    cvv
    ocvfval.v
    cW
    cbs
    fvex
    eqeltri
    #
    elpw2
    cW
    cvv
    wcel
    #
    @1
    @6
    @9
    @1
    @2
    cS
    vs
    @0
    @3
    vy
    vs
    cv
    #
    wral
    #
    vx
    cV
    crab
    #
    cmpt
    #
    cfv
    @5
    @9
    cS
    c.pe
    @13
    vx
    vy
    cF
    c.xi
    c.pe
    cV
    cW
    cvv
    c.0
    vs
    ocvfval.v
    ocvfval.i
    ocvfval.f
    ocvfval.z
    ocvfval.o
    ocvfval
    fveq1d
    vs
    cS
    @12
    @5
    @0
    @13
    @10
    cS
    wceq
    @11
    @4
    vx
    cV
    @3
    vy
    @10
    cS
    raleq
    rabbidv
    @13
    eqid
    @4
    vx
    cV
    @8
    rabex
    fvmpt
    sylan9eq
    @9
    wn
    #
    @6
    @1
    @14
    cS
    c0
    cfv
    c0
    @2
    @5
    cS
    0fv
    @14
    cS
    c.pe
    c0
    @14
    c.pe
    cW
    cocv
    cfv
    c0
    ocvfval.o
    cW
    cocv
    fvprc
    syl5eq
    fveq1d
    @14
    @5
    cV
    wss
    cV
    c0
    wceq
    @5
    c0
    wceq
    @4
    vx
    cV
    ssrab2
    @14
    cV
    @7
    c0
    ocvfval.v
    cW
    cbs
    fvprc
    syl5eq
    @5
    cV
    sseq0
    sylancr
    3eqtr4a
    adantr
    pm2.61ian
    sylbir
end
