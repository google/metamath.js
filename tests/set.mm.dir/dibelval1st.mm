include "wcel.mm"
include "wa.mm"
include "wbr.mm"
include "cfv.mm"
include "w3a.mm"
include "cltrn.mm"
include "cid.mm"
include "cres.mm"
include "cmpt.mm"
include "csn.mm"
include "cxp.mm"
include "c1st.mm"
include "eqid.mm"
include "dibval2.mm"
include "eleq2d.mm"
include "biimp3a.mm"
include "xp1st.mm"
include "syl.mm"

theorem dibelval1st
  let cB: class B
  let cH: class H
  let cI: class I
  let cJ: class J
  let cK: class K
  let c.le: class .<_
  let cV: class V
  let cW: class W
  let cX: class X
  let cY: class Y
  let vf: setvar f
  assume dibelval1.b: |- B = ( Base ` K )
  assume dibelval1.l: |- .<_ = ( le ` K )
  assume dibelval1.h: |- H = ( LHyp ` K )
  assume dibelval1.j: |- J = ( ( DIsoA ` K ) ` W )
  assume dibelval1.i: |- I = ( ( DIsoB ` K ) ` W )


  assert |- ( ( ( K e. V /\ W e. H ) /\ ( X e. B /\ X .<_ W ) /\ Y e. ( I ` X ) ) -> ( 1st ` Y ) e. ( J ` X ) )

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
    cY
    cX
    cI
    cfv
    #
    wcel
    #
    w3a
    cY
    cX
    cJ
    cfv
    #
    vf
    cW
    cK
    cltrn
    cfv
    cfv
    #
    cid
    cB
    cres
    cmpt
    #
    csn
    #
    cxp
    #
    wcel
    #
    cY
    c1st
    cfv
    @4
    wcel
    @0
    @1
    @3
    @9
    @0
    @1
    wa
    @2
    @8
    cY
    cB
    @5
    vf
    cH
    cI
    cJ
    cK
    c.le
    cV
    cW
    cX
    @6
    dibelval1.b
    dibelval1.l
    dibelval1.h
    @5
    eqid
    @6
    eqid
    dibelval1.j
    dibelval1.i
    dibval2
    eleq2d
    biimp3a
    cY
    @4
    @7
    xp1st
    syl
end
