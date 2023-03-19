include "wcel.mm"
include "wa.mm"
include "wbr.mm"
include "cfv.mm"
include "c1st.mm"
include "cdia.mm"
include "eqid.mm"
include "dibelval1st.mm"
include "diael.mm"
include "syld3an3.mm"

theorem dibelval1st1
  let cB: class B
  let cT: class T
  let cH: class H
  let cI: class I
  let cK: class K
  let c.le: class .<_
  let cV: class V
  let cW: class W
  let cX: class X
  let cY: class Y
  assume dibelval1st1.b: |- B = ( Base ` K )
  assume dibelval1st1.l: |- .<_ = ( le ` K )
  assume dibelval1st1.h: |- H = ( LHyp ` K )
  assume dibelval1st1.t: |- T = ( ( LTrn ` K ) ` W )
  assume dibelval1st1.i: |- I = ( ( DIsoB ` K ) ` W )


  assert |- ( ( ( K e. V /\ W e. H ) /\ ( X e. B /\ X .<_ W ) /\ Y e. ( I ` X ) ) -> ( 1st ` Y ) e. T )

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
    cY
    cX
    cI
    cfv
    wcel
    cY
    c1st
    cfv
    #
    cX
    cW
    cK
    cdia
    cfv
    cfv
    #
    cfv
    wcel
    @0
    cT
    wcel
    cB
    cH
    cI
    @1
    cK
    c.le
    cV
    cW
    cX
    cY
    dibelval1st1.b
    dibelval1st1.l
    dibelval1st1.h
    @1
    eqid
    #
    dibelval1st1.i
    dibelval1st
    cB
    cT
    @0
    cH
    @1
    cK
    c.le
    cV
    cW
    cX
    dibelval1st1.b
    dibelval1st1.l
    dibelval1st1.h
    dibelval1st1.t
    @2
    diael
    syld3an3
end
