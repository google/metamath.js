include "coc.mm"
include "cfv.mm"
include "cplusg.mm"
include "ctrl.mm"
include "cltrn.mm"
include "ctendo.mm"
include "cv.mm"
include "wceq.mm"
include "crio.mm"
include "cid.mm"
include "cres.mm"
include "cmpt.mm"
include "eqid.mm"
include "cdlemn11pre.mm"

theorem cdlemn11
  let cA: class A
  let cB: class B
  let c.po: class .(+)
  let cQ: class Q
  let cR: class R
  let cU: class U
  let cH: class H
  let cI: class I
  let cJ: class J
  let c.or: class .\/
  let cK: class K
  let c.le: class .<_
  let cW: class W
  let cX: class X
  let vh: setvar h
  assume cdlemn11.b: |- B = ( Base ` K )
  assume cdlemn11.l: |- .<_ = ( le ` K )
  assume cdlemn11.j: |- .\/ = ( join ` K )
  assume cdlemn11.a: |- A = ( Atoms ` K )
  assume cdlemn11.h: |- H = ( LHyp ` K )
  assume cdlemn11.i: |- I = ( ( DIsoB ` K ) ` W )
  assume cdlemn11.J: |- J = ( ( DIsoC ` K ) ` W )
  assume cdlemn11.u: |- U = ( ( DVecH ` K ) ` W )
  assume cdlemn11.s: |- .(+) = ( LSSum ` U )


  assert |- ( ( ( K e. HL /\ W e. H ) /\ ( ( Q e. A /\ -. Q .<_ W ) /\ ( R e. A /\ -. R .<_ W ) /\ ( X e. B /\ X .<_ W ) ) /\ ( J ` R ) C_ ( ( J ` Q ) .(+) ( I ` X ) ) ) -> R .<_ ( Q .\/ X ) )

  proof
    cA
    cB
    cW
    cK
    coc
    cfv
    cfv
    #
    cU
    cplusg
    cfv
    #
    c.po
    cQ
    cW
    cK
    ctrl
    cfv
    cfv
    #
    cW
    cK
    cltrn
    cfv
    cfv
    #
    cU
    vh
    cW
    cK
    ctendo
    cfv
    cfv
    #
    @0
    vh
    cv
    cfv
    #
    cQ
    wceq
    vh
    @3
    crio
    #
    @5
    cR
    wceq
    vh
    @3
    crio
    #
    cH
    cI
    cJ
    c.or
    cK
    c.le
    cR
    vh
    @3
    cid
    cB
    cres
    cmpt
    #
    cW
    cX
    cdlemn11.b
    cdlemn11.l
    cdlemn11.j
    cdlemn11.a
    cdlemn11.h
    @0
    eqid
    @8
    eqid
    @3
    eqid
    @2
    eqid
    @4
    eqid
    cdlemn11.i
    cdlemn11.J
    cdlemn11.u
    @1
    eqid
    cdlemn11.s
    @6
    eqid
    @7
    eqid
    cdlemn11pre
end
