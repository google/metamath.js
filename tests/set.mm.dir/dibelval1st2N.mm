include "wcel.mm"
include "wa.mm"
include "wbr.mm"
include "cfv.mm"
include "c1st.mm"
include "cdia.mm"
include "eqid.mm"
include "dibelval1st.mm"
include "diatrl.mm"
include "syld3an3.mm"

theorem dibelval1st2N
  let cB: class B
  let cR: class R
  let cT: class T
  let cH: class H
  let cI: class I
  let cK: class K
  let c.le: class .<_
  let cV: class V
  let cW: class W
  let cX: class X
  let cY: class Y
  assume dibelval1st2.b: |- B = ( Base ` K )
  assume dibelval1st2.l: |- .<_ = ( le ` K )
  assume dibelval1st2.h: |- H = ( LHyp ` K )
  assume dibelval1st2.t: |- T = ( ( LTrn ` K ) ` W )
  assume dibelval1st2.r: |- R = ( ( trL ` K ) ` W )
  assume dibelval1st2.i: |- I = ( ( DIsoB ` K ) ` W )


  assert |- ( ( ( K e. V /\ W e. H ) /\ ( X e. B /\ X .<_ W ) /\ Y e. ( I ` X ) ) -> ( R ` ( 1st ` Y ) ) .<_ X )

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
    cR
    cfv
    cX
    c.le
    wbr
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
    dibelval1st2.b
    dibelval1st2.l
    dibelval1st2.h
    @1
    eqid
    #
    dibelval1st2.i
    dibelval1st
    cB
    cR
    cT
    @0
    cH
    @1
    cK
    c.le
    cV
    cW
    cX
    dibelval1st2.b
    dibelval1st2.l
    dibelval1st2.h
    dibelval1st2.t
    dibelval1st2.r
    @2
    diatrl
    syld3an3
end
