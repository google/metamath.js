include "wcel.mm"
include "wa.mm"
include "wss.mm"
include "cfv.mm"
include "cpw.mm"
include "cv.mm"
include "crab.mm"
include "cmpt.mm"
include "wceq.mm"
include "dochfval.mm"
include "adantr.mm"
include "fveq1d.mm"
include "cvv.mm"
include "cbs.mm"
include "fvex.mm"
include "eqeltri.mm"
include "elpw2.mm"
include "biimpri.mm"
include "adantl.mm"
include "sseq1.mm"
include "rabbidv.mm"
include "fveq2d.mm"
include "eqid.mm"
include "fvmptg.mm"
include "sylancl.mm"
include "eqtrd.mm"

theorem dochval
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
  let cY: class Y
  let vk: setvar k
  let vw: setvar w
  let vx: setvar x
  assume dochval.b: |- B = ( Base ` K )
  assume dochval.g: |- G = ( glb ` K )
  assume dochval.o: |- ._|_ = ( oc ` K )
  assume dochval.h: |- H = ( LHyp ` K )
  assume dochval.i: |- I = ( ( DIsoH ` K ) ` W )
  assume dochval.u: |- U = ( ( DVecH ` K ) ` W )
  assume dochval.v: |- V = ( Base ` U )
  assume dochval.n: |- N = ( ( ocH ` K ) ` W )

  disjoint B y
  disjoint K y
  disjoint W y
  disjoint X y
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
  disjoint x y
  disjoint K x
  disjoint ._|_ k
  disjoint B w
  disjoint G w
  disjoint I w
  disjoint ._|_ w
  disjoint V w
  disjoint V x
  disjoint W w
  disjoint W x
  disjoint B x
  disjoint G x
  disjoint I x
  disjoint ._|_ x
  disjoint X x
  assert |- ( ( ( K e. Y /\ W e. H ) /\ X C_ V ) -> ( N ` X ) = ( I ` ( ._|_ ` ( G ` { y e. B | X C_ ( I ` y ) } ) ) ) )

  proof
    cK
    cY
    wcel
    cW
    cH
    wcel
    wa
    #
    cX
    cV
    wss
    #
    wa
    #
    cX
    cN
    cfv
    cX
    vx
    cV
    cpw
    #
    vx
    cv
    #
    vy
    cv
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
    cfv
    #
    cX
    @5
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
    @2
    cX
    cN
    @11
    @0
    cN
    @11
    wceq
    @1
    vx
    vy
    cB
    cU
    cG
    cH
    cI
    cK
    cN
    c.pe
    cV
    cW
    cY
    dochval.b
    dochval.g
    dochval.o
    dochval.h
    dochval.i
    dochval.u
    dochval.v
    dochval.n
    dochfval
    adantr
    fveq1d
    @2
    cX
    @3
    wcel
    #
    @17
    cvv
    wcel
    @12
    @17
    wceq
    @1
    @18
    @0
    @18
    @1
    cX
    cV
    cV
    cU
    cbs
    cfv
    cvv
    dochval.v
    cU
    cbs
    fvex
    eqeltri
    elpw2
    biimpri
    adantl
    @16
    cI
    fvex
    vx
    cX
    @10
    @17
    @3
    cvv
    @11
    @4
    cX
    wceq
    #
    @9
    @16
    cI
    @19
    @8
    @15
    c.pe
    @19
    @7
    @14
    cG
    @19
    @6
    @13
    vy
    cB
    @4
    cX
    @5
    sseq1
    rabbidv
    fveq2d
    fveq2d
    fveq2d
    @11
    eqid
    fvmptg
    sylancl
    eqtrd
end
