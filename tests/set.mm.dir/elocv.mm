include "cfv.mm"
include "wcel.mm"
include "wss.mm"
include "cv.mm"
include "co.mm"
include "wceq.mm"
include "wral.mm"
include "wa.mm"
include "w3a.mm"
include "cdm.mm"
include "cpw.mm"
include "elfvdm.mm"
include "crab.mm"
include "cmpt.mm"
include "cvv.mm"
include "c0.mm"
include "n0i.mm"
include "wn.mm"
include "cocv.mm"
include "fvprc.mm"
include "syl5eq.mm"
include "fveq1d.mm"
include "0fv.mm"
include "syl6eq.mm"
include "nsyl2.mm"
include "ocvfval.mm"
include "syl.mm"
include "dmeqd.mm"
include "cbs.mm"
include "fvex.mm"
include "eqeltri.mm"
include "rabex.mm"
include "eqid.mm"
include "dmmpti.mm"
include "eleqtrd.mm"
include "elpwid.mm"
include "ocvval.mm"
include "eleq2d.mm"
include "oveq1.mm"
include "eqeq1d.mm"
include "ralbidv.mm"
include "elrab.mm"
include "syl6bb.mm"
include "biadan2.mm"
include "3anass.mm"
include "bitr4i.mm"

theorem elocv
  let vx: setvar x
  let cA: class A
  let cS: class S
  let cF: class F
  let c.xi: class .,
  let c.pe: class ._|_
  let cV: class V
  let cW: class W
  let c.0: class .0.
  let vh: setvar h
  let vs: setvar s
  let vy: setvar y
  let cB: class B
  assume ocvfval.v: |- V = ( Base ` W )
  assume ocvfval.i: |- ., = ( .i ` W )
  assume ocvfval.f: |- F = ( Scalar ` W )
  assume ocvfval.z: |- .0. = ( 0g ` F )
  assume ocvfval.o: |- ._|_ = ( ocv ` W )

  disjoint .0. x
  disjoint A x
  disjoint V x
  disjoint W x
  disjoint ., x
  disjoint S x
  disjoint h s
  disjoint h x
  disjoint h y
  disjoint .0. h
  disjoint s x
  disjoint s y
  disjoint .0. s
  disjoint x y
  disjoint .0. y
  disjoint A y
  disjoint B x
  disjoint V h
  disjoint V s
  disjoint V y
  disjoint W h
  disjoint W s
  disjoint W y
  disjoint ., h
  disjoint ., s
  disjoint ., y
  disjoint S s
  disjoint S y
  assert |- ( A e. ( ._|_ ` S ) <-> ( S C_ V /\ A e. V /\ A. x e. S ( A ., x ) = .0. ) )

  proof
    cA
    cS
    c.pe
    cfv
    #
    wcel
    #
    cS
    cV
    wss
    #
    cA
    cV
    wcel
    #
    cA
    vx
    cv
    #
    c.xi
    co
    #
    c.0
    wceq
    #
    vx
    cS
    wral
    #
    wa
    #
    wa
    @2
    @3
    @7
    w3a
    @1
    @2
    @8
    @1
    cS
    cV
    @1
    cS
    c.pe
    cdm
    #
    cV
    cpw
    #
    cA
    cS
    c.pe
    elfvdm
    @1
    @9
    vs
    @10
    vy
    cv
    #
    @4
    c.xi
    co
    #
    c.0
    wceq
    #
    vx
    vs
    cv
    wral
    #
    vy
    cV
    crab
    #
    cmpt
    #
    cdm
    @10
    @1
    c.pe
    @16
    @1
    cW
    cvv
    wcel
    #
    c.pe
    @16
    wceq
    @1
    @0
    c0
    wceq
    @17
    @0
    cA
    n0i
    @17
    wn
    #
    @0
    cS
    c0
    cfv
    c0
    @18
    cS
    c.pe
    c0
    @18
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
    cS
    0fv
    syl6eq
    nsyl2
    vy
    vx
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
    syl
    dmeqd
    vs
    @10
    @15
    @16
    @14
    vy
    cV
    cV
    cW
    cbs
    cfv
    cvv
    ocvfval.v
    cW
    cbs
    fvex
    eqeltri
    rabex
    @16
    eqid
    dmmpti
    syl6eq
    eleqtrd
    elpwid
    @2
    @1
    cA
    @13
    vx
    cS
    wral
    #
    vy
    cV
    crab
    #
    wcel
    @8
    @2
    @0
    @20
    cA
    vy
    vx
    cS
    cF
    c.xi
    c.pe
    cV
    cW
    c.0
    ocvfval.v
    ocvfval.i
    ocvfval.f
    ocvfval.z
    ocvfval.o
    ocvval
    eleq2d
    @19
    @7
    vy
    cA
    cV
    @11
    cA
    wceq
    #
    @13
    @6
    vx
    cS
    @21
    @12
    @5
    c.0
    @11
    cA
    @4
    c.xi
    oveq1
    eqeq1d
    ralbidv
    elrab
    syl6bb
    biadan2
    @2
    @3
    @7
    3anass
    bitr4i
end
