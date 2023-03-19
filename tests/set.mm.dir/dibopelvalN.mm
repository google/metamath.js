include "wcel.mm"
include "wa.mm"
include "cdm.mm"
include "cop.mm"
include "cfv.mm"
include "csn.mm"
include "cxp.mm"
include "wceq.mm"
include "dibval.mm"
include "eleq2d.mm"
include "opelxp.mm"
include "cid.mm"
include "cres.mm"
include "cmpt.mm"
include "cvv.mm"
include "cltrn.mm"
include "fvex.mm"
include "eqeltri.mm"
include "mptex.mm"
include "elsn2.mm"
include "anbi2i.mm"
include "bitri.mm"
include "syl6bb.mm"

theorem dibopelvalN
  let cB: class B
  let cS: class S
  let cT: class T
  let vf: setvar f
  let cF: class F
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
  disjoint T f
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
  assert |- ( ( ( K e. V /\ W e. H ) /\ X e. dom J ) -> ( <. F , S >. e. ( I ` X ) <-> ( F e. ( J ` X ) /\ S = .0. ) ) )

  proof
    cK
    cV
    wcel
    cW
    cH
    wcel
    wa
    cX
    cJ
    cdm
    wcel
    wa
    #
    cF
    cS
    cop
    #
    cX
    cI
    cfv
    #
    wcel
    @1
    cX
    cJ
    cfv
    #
    c.0
    csn
    #
    cxp
    #
    wcel
    #
    cF
    @3
    wcel
    #
    cS
    c.0
    wceq
    #
    wa
    #
    @0
    @2
    @5
    @1
    cB
    cT
    vf
    cH
    cI
    cJ
    cK
    cV
    cW
    cX
    c.0
    dibval.b
    dibval.h
    dibval.t
    dibval.o
    dibval.j
    dibval.i
    dibval
    eleq2d
    @6
    @7
    cS
    @4
    wcel
    #
    wa
    @9
    cF
    cS
    @3
    @4
    opelxp
    @10
    @8
    @7
    cS
    c.0
    c.0
    vf
    cT
    cid
    cB
    cres
    #
    cmpt
    cvv
    dibval.o
    vf
    cT
    @11
    cT
    cW
    cK
    cltrn
    cfv
    #
    cfv
    cvv
    dibval.t
    cW
    @12
    fvex
    eqeltri
    mptex
    eqeltri
    elsn2
    anbi2i
    bitri
    syl6bb
end
