include "coc.mm"
include "cfv.mm"
include "cltrn.mm"
include "ctendo.mm"
include "cv.mm"
include "wceq.mm"
include "crio.mm"
include "clspn.mm"
include "cid.mm"
include "cres.mm"
include "cmpt.mm"
include "eqid.mm"
include "cdlemn5pre.mm"

theorem cdlemn5
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
  let cP: class P
  let cT: class T
  assume cdlemn5.b: |- B = ( Base ` K )
  assume cdlemn5.l: |- .<_ = ( le ` K )
  assume cdlemn5.j: |- .\/ = ( join ` K )
  assume cdlemn5.a: |- A = ( Atoms ` K )
  assume cdlemn5.h: |- H = ( LHyp ` K )
  assume cdlemn5.u: |- U = ( ( DVecH ` K ) ` W )
  assume cdlemn5.s: |- .(+) = ( LSSum ` U )
  assume cdlemn5.i: |- I = ( ( DIsoB ` K ) ` W )
  assume cdlemn5.J: |- J = ( ( DIsoC ` K ) ` W )


  assert |- ( ( ( K e. HL /\ W e. H ) /\ ( ( Q e. A /\ -. Q .<_ W ) /\ ( R e. A /\ -. R .<_ W ) /\ ( X e. B /\ X .<_ W ) ) /\ R .<_ ( Q .\/ X ) ) -> ( J ` R ) C_ ( ( J ` Q ) .(+) ( I ` X ) ) )

  proof
    cA
    cB
    cW
    cK
    coc
    cfv
    cfv
    #
    c.po
    cQ
    cR
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
    #
    cfv
    #
    cQ
    wceq
    vh
    @1
    crio
    #
    @4
    cR
    wceq
    vh
    @1
    crio
    #
    cH
    cI
    cJ
    c.or
    cK
    c.le
    cQ
    @3
    cfv
    cR
    wceq
    vh
    @1
    crio
    #
    cU
    clspn
    cfv
    #
    vh
    @1
    cid
    cB
    cres
    cmpt
    #
    cW
    cX
    cdlemn5.b
    cdlemn5.l
    cdlemn5.j
    cdlemn5.a
    cdlemn5.h
    cdlemn5.u
    cdlemn5.s
    cdlemn5.i
    cdlemn5.J
    @0
    eqid
    @9
    eqid
    @1
    eqid
    @2
    eqid
    @8
    eqid
    @5
    eqid
    @6
    eqid
    @7
    eqid
    cdlemn5pre
end
