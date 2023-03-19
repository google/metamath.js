include "wcel.mm"
include "cv.mm"
include "cltrn.mm"
include "cfv.mm"
include "cpw.mm"
include "cocaN.mm"
include "cin.mm"
include "cmpt2.mm"
include "cmpt.mm"
include "cdjaN.mm"
include "djaffvalN.mm"
include "fveq1d.mm"
include "syl5eq.mm"
include "wceq.mm"
include "fveq2.mm"
include "syl6eqr.mm"
include "pweqd.mm"
include "ineq12d.mm"
include "fveq12d.mm"
include "mpt2eq123dv.mm"
include "eqid.mm"
include "cvv.mm"
include "fvex.mm"
include "eqeltri.mm"
include "pwex.mm"
include "mpt2ex.mm"
include "fvmpt.mm"
include "sylan9eq.mm"

theorem djafvalN
  let vx: setvar x
  let vy: setvar y
  let cT: class T
  let cH: class H
  let cI: class I
  let cJ: class J
  let cK: class K
  let c.pe: class ._|_
  let cV: class V
  let cW: class W
  let vk: setvar k
  let vw: setvar w
  assume djaval.h: |- H = ( LHyp ` K )
  assume djaval.t: |- T = ( ( LTrn ` K ) ` W )
  assume djaval.i: |- I = ( ( DIsoA ` K ) ` W )
  assume djaval.n: |- ._|_ = ( ( ocA ` K ) ` W )
  assume djaval.j: |- J = ( ( vA ` K ) ` W )

  disjoint x y
  disjoint K x
  disjoint K y
  disjoint T x
  disjoint T y
  disjoint W x
  disjoint W y
  disjoint k w
  disjoint H k
  disjoint H w
  disjoint k x
  disjoint k y
  disjoint K k
  disjoint w x
  disjoint w y
  disjoint K w
  disjoint ._|_ w
  disjoint T w
  disjoint W w
  assert |- ( ( K e. V /\ W e. H ) -> J = ( x e. ~P T , y e. ~P T |-> ( ._|_ ` ( ( ._|_ ` x ) i^i ( ._|_ ` y ) ) ) ) )

  proof
    cK
    cV
    wcel
    #
    cW
    cH
    wcel
    cJ
    cW
    vw
    cH
    vx
    vy
    vw
    cv
    #
    cK
    cltrn
    cfv
    #
    cfv
    #
    cpw
    #
    @4
    vx
    cv
    #
    @1
    cK
    cocaN
    cfv
    #
    cfv
    #
    cfv
    #
    vy
    cv
    #
    @7
    cfv
    #
    cin
    #
    @7
    cfv
    #
    cmpt2
    #
    cmpt
    #
    cfv
    #
    vx
    vy
    cT
    cpw
    #
    @16
    @5
    c.pe
    cfv
    #
    @9
    c.pe
    cfv
    #
    cin
    #
    c.pe
    cfv
    #
    cmpt2
    #
    @0
    cJ
    cW
    cK
    cdjaN
    cfv
    #
    cfv
    @15
    djaval.j
    @0
    cW
    @22
    @14
    vx
    vy
    vw
    cH
    cK
    cV
    djaval.h
    djaffvalN
    fveq1d
    syl5eq
    vw
    cW
    @13
    @21
    cH
    @14
    @1
    cW
    wceq
    #
    vx
    vy
    @4
    @4
    @12
    @16
    @16
    @20
    @23
    @3
    cT
    @23
    @3
    cW
    @2
    cfv
    #
    cT
    @1
    cW
    @2
    fveq2
    djaval.t
    syl6eqr
    pweqd
    #
    @25
    @23
    @11
    @19
    @7
    c.pe
    @23
    @7
    cW
    @6
    cfv
    c.pe
    @1
    cW
    @6
    fveq2
    djaval.n
    syl6eqr
    #
    @23
    @8
    @17
    @10
    @18
    @23
    @5
    @7
    c.pe
    @26
    fveq1d
    @23
    @9
    @7
    c.pe
    @26
    fveq1d
    ineq12d
    fveq12d
    mpt2eq123dv
    @14
    eqid
    vx
    vy
    @16
    @16
    @20
    cT
    cT
    @24
    cvv
    djaval.t
    cW
    @2
    fvex
    eqeltri
    pwex
    #
    @27
    mpt2ex
    fvmpt
    sylan9eq
end
