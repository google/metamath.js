include "wcel.mm"
include "wa.mm"
include "wbr.mm"
include "cdm.mm"
include "cfv.mm"
include "csn.mm"
include "cxp.mm"
include "wceq.mm"
include "diaeldm.mm"
include "biimpar.mm"
include "dibval.mm"
include "syldan.mm"

theorem dibval2
  let cB: class B
  let cT: class T
  let vf: setvar f
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
  assert |- ( ( ( K e. V /\ W e. H ) /\ ( X e. B /\ X .<_ W ) ) -> ( I ` X ) = ( ( J ` X ) X. { .0. } ) )

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
    cB
    wcel
    cX
    cW
    c.le
    wbr
    wa
    #
    cX
    cJ
    cdm
    wcel
    #
    cX
    cI
    cfv
    cX
    cJ
    cfv
    c.0
    csn
    cxp
    wceq
    @0
    @2
    @1
    cB
    cH
    cJ
    cK
    c.le
    cV
    cW
    cX
    dibval2.b
    dibval2.l
    dibval2.h
    dibval2.j
    diaeldm
    biimpar
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
    dibval2.b
    dibval2.h
    dibval2.t
    dibval2.o
    dibval2.j
    dibval2.i
    dibval
    syldan
end
