include "wcel.mm"
include "wa.mm"
include "wbr.mm"
include "cop.mm"
include "cfv.mm"
include "cdia.mm"
include "wceq.mm"
include "eqid.mm"
include "dibopelval2.mm"
include "diaelval.mm"
include "anbi1d.mm"
include "bitrd.mm"

theorem dibopelval3
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
  let cV: class V
  let cW: class W
  let cX: class X
  let c.0: class .0.
  let vf: setvar f
  let vs: setvar s
  let cY: class Y
  assume dibval3.b: |- B = ( Base ` K )
  assume dibval3.l: |- .<_ = ( le ` K )
  assume dibval3.h: |- H = ( LHyp ` K )
  assume dibval3.t: |- T = ( ( LTrn ` K ) ` W )
  assume dibval3.r: |- R = ( ( trL ` K ) ` W )
  assume dibval3.o: |- .0. = ( g e. T |-> ( _I |` B ) )
  assume dibval3.i: |- I = ( ( DIsoB ` K ) ` W )

  disjoint K g
  disjoint W g
  disjoint T g
  disjoint K f
  disjoint T f
  disjoint W f
  disjoint X f
  disjoint .<_ f
  disjoint B f
  disjoint H f
  disjoint K s
  disjoint f s
  disjoint .0. f
  disjoint .0. s
  disjoint V f
  disjoint W s
  disjoint X s
  disjoint Y f
  disjoint Y s
  assert |- ( ( ( K e. V /\ W e. H ) /\ ( X e. B /\ X .<_ W ) ) -> ( <. F , S >. e. ( I ` X ) <-> ( ( F e. T /\ ( R ` F ) .<_ X ) /\ S = .0. ) ) )

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
    cX
    cI
    cfv
    wcel
    cF
    cX
    cW
    cK
    cdia
    cfv
    cfv
    #
    cfv
    wcel
    #
    cS
    c.0
    wceq
    #
    wa
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
    #
    @3
    wa
    cB
    cS
    cT
    vg
    cF
    cH
    cI
    @1
    cK
    c.le
    cV
    cW
    cX
    c.0
    dibval3.b
    dibval3.l
    dibval3.h
    dibval3.t
    dibval3.o
    @1
    eqid
    #
    dibval3.i
    dibopelval2
    @0
    @2
    @4
    @3
    cB
    cR
    cT
    cF
    cH
    @1
    cK
    c.le
    cV
    cW
    cX
    dibval3.b
    dibval3.l
    dibval3.h
    dibval3.t
    dibval3.r
    @5
    diaelval
    anbi1d
    bitrd
end
