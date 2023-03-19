include "wcel.mm"
include "cocv.mm"
include "cfv.mm"
include "cpw.mm"
include "cv.mm"
include "co.mm"
include "wceq.mm"
include "wral.mm"
include "crab.mm"
include "cmpt.mm"
include "cvv.mm"
include "elex.mm"
include "cbs.mm"
include "cip.mm"
include "csca.mm"
include "c0g.mm"
include "fveq2.mm"
include "syl6eqr.mm"
include "pweqd.mm"
include "oveqd.mm"
include "fveq2d.mm"
include "eqeq12d.mm"
include "ralbidv.mm"
include "rabeqbidv.mm"
include "mpteq12dv.mm"
include "df-ocv.mm"
include "wf.mm"
include "eqid.mm"
include "wss.mm"
include "ssrab2.mm"
include "fvex.mm"
include "eqeltri.mm"
include "elpw2.mm"
include "mpbir.mm"
include "a1i.mm"
include "fmpti.mm"
include "pwex.mm"
include "fex2.mm"
include "mp3an.mm"
include "fvmpt.mm"
include "syl.mm"
include "syl5eq.mm"

theorem ocvfval
  let vx: setvar x
  let vy: setvar y
  let cF: class F
  let c.xi: class .,
  let c.pe: class ._|_
  let cV: class V
  let cW: class W
  let cX: class X
  let c.0: class .0.
  let vs: setvar s
  let vh: setvar h
  let cA: class A
  let cB: class B
  let cS: class S
  assume ocvfval.v: |- V = ( Base ` W )
  assume ocvfval.i: |- ., = ( .i ` W )
  assume ocvfval.f: |- F = ( Scalar ` W )
  assume ocvfval.z: |- .0. = ( 0g ` F )
  assume ocvfval.o: |- ._|_ = ( ocv ` W )

  disjoint s x
  disjoint s y
  disjoint .0. s
  disjoint x y
  disjoint .0. x
  disjoint .0. y
  disjoint V s
  disjoint V x
  disjoint V y
  disjoint W s
  disjoint W x
  disjoint W y
  disjoint ., s
  disjoint ., x
  disjoint ., y
  disjoint h s
  disjoint h x
  disjoint h y
  disjoint .0. h
  disjoint A x
  disjoint A y
  disjoint B x
  disjoint V h
  disjoint W h
  disjoint ., h
  disjoint S s
  disjoint S x
  disjoint S y
  assert |- ( W e. X -> ._|_ = ( s e. ~P V |-> { x e. V | A. y e. s ( x ., y ) = .0. } ) )

  proof
    cW
    cX
    wcel
    #
    c.pe
    cW
    cocv
    cfv
    #
    vs
    cV
    cpw
    #
    vx
    cv
    #
    vy
    cv
    #
    c.xi
    co
    #
    c.0
    wceq
    #
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
    ocvfval.o
    @0
    cW
    cvv
    wcel
    @1
    @10
    wceq
    cW
    cX
    elex
    vh
    cW
    vs
    vh
    cv
    #
    cbs
    cfv
    #
    cpw
    #
    @3
    @4
    @11
    cip
    cfv
    #
    co
    #
    @11
    csca
    cfv
    #
    c0g
    cfv
    #
    wceq
    #
    vy
    @7
    wral
    #
    vx
    @12
    crab
    #
    cmpt
    @10
    cvv
    cocv
    @11
    cW
    wceq
    #
    vs
    @13
    @20
    @2
    @9
    @21
    @12
    cV
    @21
    @12
    cW
    cbs
    cfv
    #
    cV
    @11
    cW
    cbs
    fveq2
    ocvfval.v
    syl6eqr
    #
    pweqd
    @21
    @19
    @8
    vx
    @12
    cV
    @23
    @21
    @18
    @6
    vy
    @7
    @21
    @15
    @5
    @17
    c.0
    @21
    @14
    c.xi
    @3
    @4
    @21
    @14
    cW
    cip
    cfv
    c.xi
    @11
    cW
    cip
    fveq2
    ocvfval.i
    syl6eqr
    oveqd
    @21
    @17
    cF
    c0g
    cfv
    c.0
    @21
    @16
    cF
    c0g
    @21
    @16
    cW
    csca
    cfv
    cF
    @11
    cW
    csca
    fveq2
    ocvfval.f
    syl6eqr
    fveq2d
    ocvfval.z
    syl6eqr
    eqeq12d
    ralbidv
    rabeqbidv
    mpteq12dv
    vx
    vy
    vh
    vs
    df-ocv
    @2
    @2
    @10
    wf
    @2
    cvv
    wcel
    #
    @24
    @10
    cvv
    wcel
    vs
    @2
    @2
    @9
    @10
    @10
    eqid
    @9
    @2
    wcel
    #
    @7
    @2
    wcel
    @25
    @9
    cV
    wss
    @8
    vx
    cV
    ssrab2
    @9
    cV
    cV
    @22
    cvv
    ocvfval.v
    cW
    cbs
    fvex
    eqeltri
    #
    elpw2
    mpbir
    a1i
    fmpti
    cV
    @26
    pwex
    #
    @27
    @2
    @2
    @10
    cvv
    cvv
    fex2
    mp3an
    fvmpt
    syl
    syl5eq
end
