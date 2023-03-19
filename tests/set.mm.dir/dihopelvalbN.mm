include "wcel.mm"
include "wa.mm"
include "wbr.mm"
include "cop.mm"
include "cfv.mm"
include "cdib.mm"
include "wceq.mm"
include "eqid.mm"
include "dihvalb.mm"
include "eleq2d.mm"
include "dibopelval3.mm"
include "bitrd.mm"

theorem dihopelvalbN
  let cB: class B
  let cR: class R
  let cS: class S
  let cT: class T
  let vg: setvar g
  let cF: class F
  let cH: class H
  let cI: class I
  let cK: class K
  let c.le: class .<_
  let cO: class O
  let cV: class V
  let cW: class W
  let cX: class X
  assume dihval3.b: |- B = ( Base ` K )
  assume dihval3.l: |- .<_ = ( le ` K )
  assume dihval3.h: |- H = ( LHyp ` K )
  assume dihval3.t: |- T = ( ( LTrn ` K ) ` W )
  assume dihval3.r: |- R = ( ( trL ` K ) ` W )
  assume dihval3.o: |- O = ( g e. T |-> ( _I |` B ) )
  assume dihval3.i: |- I = ( ( DIsoH ` K ) ` W )

  disjoint K g
  disjoint T g
  disjoint W g
  assert |- ( ( ( K e. V /\ W e. H ) /\ ( X e. B /\ X .<_ W ) ) -> ( <. F , S >. e. ( I ` X ) <-> ( ( F e. T /\ ( R ` F ) .<_ X ) /\ S = O ) ) )

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
    cW
    cK
    cdib
    cfv
    cfv
    #
    cfv
    #
    wcel
    cF
    cT
    wcel
    cF
    cR
    cfv
    cX
    c.le
    wbr
    wa
    cS
    cO
    wceq
    wa
    @0
    @2
    @4
    @1
    cB
    @3
    cH
    cI
    cK
    c.le
    cV
    cW
    cX
    dihval3.b
    dihval3.l
    dihval3.h
    dihval3.i
    @3
    eqid
    #
    dihvalb
    eleq2d
    cB
    cR
    cS
    cT
    vg
    cF
    cH
    @3
    cK
    c.le
    cV
    cW
    cX
    cO
    dihval3.b
    dihval3.l
    dihval3.h
    dihval3.t
    dihval3.r
    dihval3.o
    @5
    dibopelval3
    bitrd
end
