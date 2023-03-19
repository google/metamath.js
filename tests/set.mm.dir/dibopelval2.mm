include "wcel.mm"
include "wa.mm"
include "wbr.mm"
include "cop.mm"
include "cfv.mm"
include "csn.mm"
include "cxp.mm"
include "wceq.mm"
include "dibval2.mm"
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

theorem dibopelval2
  let cB: class B
  let cS: class S
  let cT: class T
  let vf: setvar f
  let cF: class F
  let cH: class H
  let cI: class I
  let cJ: class J
  let cK: class K
  let c.le: class .<_
  let cV: class V
  let cW: class W
  let cX: class X
  let c.0: class .0.
  assume dibval2.b: |- B = ( Base ` K )
  assume dibval2.l: |- .<_ = ( le ` K )
  assume dibval2.h: |- H = ( LHyp ` K )
  assume dibval2.t: |- T = ( ( LTrn ` K ) ` W )
  assume dibval2.o: |- .0. = ( f e. T |-> ( _I |` B ) )
  assume dibval2.j: |- J = ( ( DIsoA ` K ) ` W )
  assume dibval2.i: |- I = ( ( DIsoB ` K ) ` W )

  disjoint K f
  disjoint W f
  disjoint T f
  assert |- ( ( ( K e. V /\ W e. H ) /\ ( X e. B /\ X .<_ W ) ) -> ( <. F , S >. e. ( I ` X ) <-> ( F e. ( J ` X ) /\ S = .0. ) ) )

  proof
    cK
    cV
    wcel
    cW
    cH
    wcel
    wa
    cX
    cB
    wcel
    cX
    cW
    c.le
    wbr
    wa
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
    c.le
    cV
    cW
    cX
    c.0
    dibval2.b
    dibval2.l
    dibval2.h
    dibval2.t
    dibval2.o
    dibval2.j
    dibval2.i
    dibval2
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
    dibval2.o
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
    dibval2.t
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
