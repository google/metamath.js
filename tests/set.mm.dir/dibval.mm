include "wcel.mm"
include "wa.mm"
include "cdm.mm"
include "cfv.mm"
include "cv.mm"
include "csn.mm"
include "cxp.mm"
include "cmpt.mm"
include "wceq.mm"
include "dibfval.mm"
include "adantr.mm"
include "fveq1d.mm"
include "fveq2.mm"
include "xpeq1d.mm"
include "eqid.mm"
include "fvex.mm"
include "snex.mm"
include "xpex.mm"
include "fvmpt.mm"
include "adantl.mm"
include "eqtrd.mm"

theorem dibval
  let cB: class B
  let cT: class T
  let vf: setvar f
  let cH: class H
  let cI: class I
  let cJ: class J
  let cK: class K
  let cV: class V
  let cW: class W
  let cX: class X
  let c.0: class .0.
  let vk: setvar k
  let vw: setvar w
  let vx: setvar x
  assume dibval.b: |- B = ( Base ` K )
  assume dibval.h: |- H = ( LHyp ` K )
  assume dibval.t: |- T = ( ( LTrn ` K ) ` W )
  assume dibval.o: |- .0. = ( f e. T |-> ( _I |` B ) )
  assume dibval.j: |- J = ( ( DIsoA ` K ) ` W )
  assume dibval.i: |- I = ( ( DIsoB ` K ) ` W )

  disjoint K f
  disjoint W f
  disjoint B k
  disjoint k w
  disjoint H k
  disjoint H w
  disjoint f k
  disjoint f w
  disjoint f x
  disjoint k x
  disjoint K k
  disjoint w x
  disjoint K w
  disjoint K x
  disjoint J w
  disjoint J x
  disjoint .0. w
  disjoint W w
  disjoint W x
  disjoint .0. x
  disjoint X x
  assert |- ( ( ( K e. V /\ W e. H ) /\ X e. dom J ) -> ( I ` X ) = ( ( J ` X ) X. { .0. } ) )

  proof
    cK
    cV
    wcel
    cW
    cH
    wcel
    wa
    #
    cX
    cJ
    cdm
    #
    wcel
    #
    wa
    #
    cX
    cI
    cfv
    cX
    vx
    @1
    vx
    cv
    #
    cJ
    cfv
    #
    c.0
    csn
    #
    cxp
    #
    cmpt
    #
    cfv
    #
    cX
    cJ
    cfv
    #
    @6
    cxp
    #
    @3
    cX
    cI
    @8
    @0
    cI
    @8
    wceq
    @2
    vx
    cB
    cT
    vf
    cH
    cI
    cJ
    cK
    cV
    cW
    c.0
    dibval.b
    dibval.h
    dibval.t
    dibval.o
    dibval.j
    dibval.i
    dibfval
    adantr
    fveq1d
    @2
    @9
    @11
    wceq
    @0
    vx
    cX
    @7
    @11
    @1
    @8
    @4
    cX
    wceq
    @5
    @10
    @6
    @4
    cX
    cJ
    fveq2
    xpeq1d
    @8
    eqid
    @10
    @6
    cX
    cJ
    fvex
    c.0
    snex
    xpex
    fvmpt
    adantl
    eqtrd
end
