include "chlt.mm"
include "wcel.mm"
include "wa.mm"
include "wbr.mm"
include "wn.mm"
include "w3a.mm"
include "co.mm"
include "wceq.mm"
include "cfv.mm"
include "wss.mm"
include "coc.mm"
include "cplusg.mm"
include "ctrl.mm"
include "cltrn.mm"
include "ctendo.mm"
include "cv.mm"
include "crio.mm"
include "cid.mm"
include "cres.mm"
include "cmpt.mm"
include "eqid.mm"
include "dihord2pre2.mm"
include "simp31.mm"
include "simp32.mm"
include "3brtr3d.mm"

theorem dihord2
  let cA: class A
  let cB: class B
  let c.po: class .(+)
  let cQ: class Q
  let cU: class U
  let cH: class H
  let cI: class I
  let cJ: class J
  let c.or: class .\/
  let cK: class K
  let c.le: class .<_
  let c.an: class ./\
  let cN: class N
  let cW: class W
  let cX: class X
  let cY: class Y
  let vh: setvar h
  assume dihord2.b: |- B = ( Base ` K )
  assume dihord2.l: |- .<_ = ( le ` K )
  assume dihord2.j: |- .\/ = ( join ` K )
  assume dihord2.m: |- ./\ = ( meet ` K )
  assume dihord2.a: |- A = ( Atoms ` K )
  assume dihord2.h: |- H = ( LHyp ` K )
  assume dihord2.i: |- I = ( ( DIsoB ` K ) ` W )
  assume dihord2.J: |- J = ( ( DIsoC ` K ) ` W )
  assume dihord2.u: |- U = ( ( DVecH ` K ) ` W )
  assume dihord2.s: |- .(+) = ( LSSum ` U )


  assert |- ( ( ( ( K e. HL /\ W e. H ) /\ ( Q e. A /\ -. Q .<_ W ) /\ ( N e. A /\ -. N .<_ W ) ) /\ ( X e. B /\ Y e. B ) /\ ( ( Q .\/ ( X ./\ W ) ) = X /\ ( N .\/ ( Y ./\ W ) ) = Y /\ ( ( J ` Q ) .(+) ( I ` ( X ./\ W ) ) ) C_ ( ( J ` N ) .(+) ( I ` ( Y ./\ W ) ) ) ) ) -> X .<_ Y )

  proof
    cK
    chlt
    wcel
    cW
    cH
    wcel
    wa
    cQ
    cA
    wcel
    cQ
    cW
    c.le
    wbr
    wn
    wa
    cN
    cA
    wcel
    cN
    cW
    c.le
    wbr
    wn
    wa
    w3a
    #
    cX
    cB
    wcel
    cY
    cB
    wcel
    wa
    #
    cQ
    cX
    cW
    c.an
    co
    #
    c.or
    co
    #
    cX
    wceq
    #
    cN
    cY
    cW
    c.an
    co
    #
    c.or
    co
    #
    cY
    wceq
    #
    cQ
    cJ
    cfv
    @2
    cI
    cfv
    c.po
    co
    cN
    cJ
    cfv
    @5
    cI
    cfv
    c.po
    co
    wss
    #
    w3a
    w3a
    @3
    @6
    cX
    cY
    c.le
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
    @9
    vh
    cv
    cfv
    cN
    wceq
    vh
    @12
    crio
    #
    cH
    cI
    cJ
    c.or
    cK
    c.le
    c.an
    cN
    vh
    @12
    cid
    cB
    cres
    cmpt
    #
    cW
    cX
    cY
    dihord2.b
    dihord2.l
    dihord2.j
    dihord2.m
    dihord2.a
    dihord2.h
    dihord2.i
    dihord2.J
    dihord2.u
    dihord2.s
    @12
    eqid
    @11
    eqid
    @15
    eqid
    @9
    eqid
    @13
    eqid
    @10
    eqid
    @14
    eqid
    dihord2pre2
    @0
    @1
    @4
    @7
    @8
    simp31
    @0
    @1
    @4
    @7
    @8
    simp32
    3brtr3d
end
