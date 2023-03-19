include "wcel.mm"
include "wa.mm"
include "wbr.mm"
include "cfv.mm"
include "w3a.mm"
include "cdia.mm"
include "csn.mm"
include "cxp.mm"
include "c2nd.mm"
include "wceq.mm"
include "eqid.mm"
include "dibval2.mm"
include "eleq2d.mm"
include "biimp3a.mm"
include "xp2nd.mm"
include "elsni.mm"
include "3syl.mm"

theorem dibelval2nd
  let cB: class B
  let cT: class T
  let vf: setvar f
  let cH: class H
  let cI: class I
  let cK: class K
  let c.le: class .<_
  let cV: class V
  let cW: class W
  let cX: class X
  let cY: class Y
  let c.0: class .0.
  assume dibelval2nd.b: |- B = ( Base ` K )
  assume dibelval2nd.l: |- .<_ = ( le ` K )
  assume dibelval2nd.h: |- H = ( LHyp ` K )
  assume dibelval2nd.t: |- T = ( ( LTrn ` K ) ` W )
  assume dibelval2nd.o: |- .0. = ( f e. T |-> ( _I |` B ) )
  assume dibelval2nd.i: |- I = ( ( DIsoB ` K ) ` W )

  disjoint K f
  disjoint W f
  assert |- ( ( ( K e. V /\ W e. H ) /\ ( X e. B /\ X .<_ W ) /\ Y e. ( I ` X ) ) -> ( 2nd ` Y ) = .0. )

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
    #
    wcel
    #
    cY
    c2nd
    cfv
    #
    @6
    wcel
    @9
    c.0
    wceq
    @0
    @1
    @3
    @8
    @0
    @1
    wa
    @2
    @7
    cY
    cB
    cT
    vf
    cH
    cI
    @4
    cK
    c.le
    cV
    cW
    cX
    c.0
    dibelval2nd.b
    dibelval2nd.l
    dibelval2nd.h
    dibelval2nd.t
    dibelval2nd.o
    @4
    eqid
    dibelval2nd.i
    dibval2
    eleq2d
    biimp3a
    cY
    @5
    @6
    xp2nd
    @9
    c.0
    elsni
    3syl
end
