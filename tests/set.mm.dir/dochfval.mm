include "wcel.mm"
include "cv.mm"
include "cdvh.mm"
include "cfv.mm"
include "cbs.mm"
include "cpw.mm"
include "cdih.mm"
include "wss.mm"
include "crab.mm"
include "cmpt.mm"
include "coch.mm"
include "dochffval.mm"
include "fveq1d.mm"
include "syl5eq.mm"
include "wceq.mm"
include "fveq2.mm"
include "syl6eqr.mm"
include "fveq2d.mm"
include "pweqd.mm"
include "sseq2d.mm"
include "rabbidv.mm"
include "fveq12d.mm"
include "mpteq12dv.mm"
include "eqid.mm"
include "cvv.mm"
include "fvex.mm"
include "eqeltri.mm"
include "pwex.mm"
include "mptex.mm"
include "fvmpt.mm"
include "sylan9eq.mm"

theorem dochfval
  let vx: setvar x
  let vy: setvar y
  let cB: class B
  let cU: class U
  let cG: class G
  let cH: class H
  let cI: class I
  let cK: class K
  let cN: class N
  let c.pe: class ._|_
  let cV: class V
  let cW: class W
  let cX: class X
  let vk: setvar k
  let vw: setvar w
  assume dochval.b: |- B = ( Base ` K )
  assume dochval.g: |- G = ( glb ` K )
  assume dochval.o: |- ._|_ = ( oc ` K )
  assume dochval.h: |- H = ( LHyp ` K )
  assume dochval.i: |- I = ( ( DIsoH ` K ) ` W )
  assume dochval.u: |- U = ( ( DVecH ` K ) ` W )
  assume dochval.v: |- V = ( Base ` U )
  assume dochval.n: |- N = ( ( ocH ` K ) ` W )

  disjoint B y
  disjoint x y
  disjoint K x
  disjoint K y
  disjoint V x
  disjoint W x
  disjoint W y
  disjoint k y
  disjoint B k
  disjoint G k
  disjoint k w
  disjoint H k
  disjoint H w
  disjoint k x
  disjoint K k
  disjoint w x
  disjoint w y
  disjoint K w
  disjoint ._|_ k
  disjoint B w
  disjoint G w
  disjoint I w
  disjoint ._|_ w
  disjoint V w
  disjoint W w
  assert |- ( ( K e. X /\ W e. H ) -> N = ( x e. ~P V |-> ( I ` ( ._|_ ` ( G ` { y e. B | x C_ ( I ` y ) } ) ) ) ) )

  proof
    cK
    cX
    wcel
    #
    cW
    cH
    wcel
    cN
    cW
    vw
    cH
    vx
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
    vx
    cv
    #
    vy
    cv
    #
    @1
    cK
    cdih
    cfv
    #
    cfv
    #
    cfv
    #
    wss
    #
    vy
    cB
    crab
    #
    cG
    cfv
    #
    c.pe
    cfv
    #
    @9
    cfv
    #
    cmpt
    #
    cmpt
    #
    cfv
    #
    vx
    cV
    cpw
    #
    @6
    @7
    cI
    cfv
    #
    wss
    #
    vy
    cB
    crab
    #
    cG
    cfv
    #
    c.pe
    cfv
    #
    cI
    cfv
    #
    cmpt
    #
    @0
    cN
    cW
    cK
    coch
    cfv
    #
    cfv
    @18
    dochval.n
    @0
    cW
    @27
    @17
    vx
    vy
    vw
    cB
    cG
    cH
    cK
    c.pe
    cX
    dochval.b
    dochval.g
    dochval.o
    dochval.h
    dochffval
    fveq1d
    syl5eq
    vw
    cW
    @16
    @26
    cH
    @17
    @1
    cW
    wceq
    #
    vx
    @5
    @15
    @19
    @25
    @28
    @4
    cV
    @28
    @4
    cU
    cbs
    cfv
    #
    cV
    @28
    @3
    cU
    cbs
    @28
    @3
    cW
    @2
    cfv
    cU
    @1
    cW
    @2
    fveq2
    dochval.u
    syl6eqr
    fveq2d
    dochval.v
    syl6eqr
    pweqd
    @28
    @14
    @24
    @9
    cI
    @28
    @9
    cW
    @8
    cfv
    cI
    @1
    cW
    @8
    fveq2
    dochval.i
    syl6eqr
    #
    @28
    @13
    @23
    c.pe
    @28
    @12
    @22
    cG
    @28
    @11
    @21
    vy
    cB
    @28
    @10
    @20
    @6
    @28
    @7
    @9
    cI
    @30
    fveq1d
    sseq2d
    rabbidv
    fveq2d
    fveq2d
    fveq12d
    mpteq12dv
    @17
    eqid
    vx
    @19
    @25
    cV
    cV
    @29
    cvv
    dochval.v
    cU
    cbs
    fvex
    eqeltri
    pwex
    mptex
    fvmpt
    sylan9eq
end
