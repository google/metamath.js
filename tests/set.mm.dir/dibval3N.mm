include "wcel.mm"
include "wa.mm"
include "wbr.mm"
include "cfv.mm"
include "cdia.mm"
include "csn.mm"
include "cxp.mm"
include "cv.mm"
include "crab.mm"
include "eqid.mm"
include "dibval2.mm"
include "diaval.mm"
include "xpeq1d.mm"
include "eqtrd.mm"

theorem dibval3N
  let cB: class B
  let cR: class R
  let cT: class T
  let vf: setvar f
  let vg: setvar g
  let cH: class H
  let cI: class I
  let cK: class K
  let c.le: class .<_
  let cV: class V
  let cW: class W
  let cX: class X
  let c.0: class .0.
  assume dibval3.b: |- B = ( Base ` K )
  assume dibval3.l: |- .<_ = ( le ` K )
  assume dibval3.h: |- H = ( LHyp ` K )
  assume dibval3.t: |- T = ( ( LTrn ` K ) ` W )
  assume dibval3.r: |- R = ( ( trL ` K ) ` W )
  assume dibval3.o: |- .0. = ( g e. T |-> ( _I |` B ) )
  assume dibval3.i: |- I = ( ( DIsoB ` K ) ` W )

  disjoint K f
  disjoint K g
  disjoint T f
  disjoint W f
  disjoint W g
  disjoint X f
  assert |- ( ( ( K e. V /\ W e. H ) /\ ( X e. B /\ X .<_ W ) ) -> ( I ` X ) = ( { f e. T | ( R ` f ) .<_ X } X. { .0. } ) )

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
    cX
    cI
    cfv
    cX
    cW
    cK
    cdia
    cfv
    cfv
    #
    cfv
    #
    c.0
    csn
    #
    cxp
    vf
    cv
    cR
    cfv
    cX
    c.le
    wbr
    vf
    cT
    crab
    #
    @3
    cxp
    cB
    cT
    vg
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
    dibval2
    @0
    @2
    @4
    @3
    cB
    cR
    cT
    vf
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
    diaval
    xpeq1d
    eqtrd
end
