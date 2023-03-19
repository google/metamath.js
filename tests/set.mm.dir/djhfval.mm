include "wcel.mm"
include "cv.mm"
include "cdvh.mm"
include "cfv.mm"
include "cbs.mm"
include "cpw.mm"
include "coch.mm"
include "cin.mm"
include "cmpt2.mm"
include "cmpt.mm"
include "cdjh.mm"
include "djhffval.mm"
include "fveq1d.mm"
include "syl5eq.mm"
include "wceq.mm"
include "fveq2.mm"
include "fveq2d.mm"
include "fveq2i.mm"
include "eqtri.mm"
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

theorem djhfval
  let vx: setvar x
  let vy: setvar y
  let cU: class U
  let cH: class H
  let c.or: class .\/
  let cK: class K
  let c.pe: class ._|_
  let cV: class V
  let cW: class W
  let cX: class X
  let vk: setvar k
  let vw: setvar w
  assume djhval.h: |- H = ( LHyp ` K )
  assume djhval.u: |- U = ( ( DVecH ` K ) ` W )
  assume djhval.v: |- V = ( Base ` U )
  assume djhval.o: |- ._|_ = ( ( ocH ` K ) ` W )
  assume djhval.j: |- .\/ = ( ( joinH ` K ) ` W )

  disjoint x y
  disjoint K x
  disjoint K y
  disjoint V x
  disjoint V y
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
  disjoint V w
  disjoint W w
  assert |- ( ( K e. X /\ W e. H ) -> .\/ = ( x e. ~P V , y e. ~P V |-> ( ._|_ ` ( ( ._|_ ` x ) i^i ( ._|_ ` y ) ) ) ) )

  proof
    cK
    cX
    wcel
    #
    cW
    cH
    wcel
    c.or
    cW
    vw
    cH
    vx
    vy
    vw
    cv
    #
    cK
    cdvh
    cfv
    #
    cfv
    #
    cbs
    cfv
    #
    cpw
    #
    @5
    vx
    cv
    #
    @1
    cK
    coch
    cfv
    #
    cfv
    #
    cfv
    #
    vy
    cv
    #
    @8
    cfv
    #
    cin
    #
    @8
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
    cV
    cpw
    #
    @17
    @6
    c.pe
    cfv
    #
    @10
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
    c.or
    cW
    cK
    cdjh
    cfv
    #
    cfv
    @16
    djhval.j
    @0
    cW
    @23
    @15
    vx
    vy
    vw
    cH
    cK
    cX
    djhval.h
    djhffval
    fveq1d
    syl5eq
    vw
    cW
    @14
    @22
    cH
    @15
    @1
    cW
    wceq
    #
    vx
    vy
    @5
    @5
    @13
    @17
    @17
    @21
    @24
    @4
    cV
    @24
    @4
    cW
    @2
    cfv
    #
    cbs
    cfv
    #
    cV
    @24
    @3
    @25
    cbs
    @1
    cW
    @2
    fveq2
    fveq2d
    cV
    cU
    cbs
    cfv
    #
    @26
    djhval.v
    cU
    @25
    cbs
    djhval.u
    fveq2i
    eqtri
    syl6eqr
    pweqd
    #
    @28
    @24
    @12
    @20
    @8
    c.pe
    @24
    @8
    cW
    @7
    cfv
    c.pe
    @1
    cW
    @7
    fveq2
    djhval.o
    syl6eqr
    #
    @24
    @9
    @18
    @11
    @19
    @24
    @6
    @8
    c.pe
    @29
    fveq1d
    @24
    @10
    @8
    c.pe
    @29
    fveq1d
    ineq12d
    fveq12d
    mpt2eq123dv
    @15
    eqid
    vx
    vy
    @17
    @17
    @21
    cV
    cV
    @27
    cvv
    djhval.v
    cU
    cbs
    fvex
    eqeltri
    pwex
    #
    @30
    mpt2ex
    fvmpt
    sylan9eq
end
