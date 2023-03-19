include "chlt.mm"
include "wcel.mm"
include "wa.mm"
include "wbr.mm"
include "wn.mm"
include "w3a.mm"
include "co.mm"
include "wceq.mm"
include "cfv.mm"
include "dihjustlem.mm"
include "wss.mm"
include "simp1.mm"
include "simp22.mm"
include "simp21.mm"
include "simp23.mm"
include "simp3.mm"
include "eqcomd.mm"
include "syl131anc.mm"
include "eqssd.mm"

theorem dihjust
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
  let c.an: class ./\
  let cW: class W
  let cX: class X
  assume dihjust.b: |- B = ( Base ` K )
  assume dihjust.l: |- .<_ = ( le ` K )
  assume dihjust.j: |- .\/ = ( join ` K )
  assume dihjust.m: |- ./\ = ( meet ` K )
  assume dihjust.a: |- A = ( Atoms ` K )
  assume dihjust.h: |- H = ( LHyp ` K )
  assume dihjust.i: |- I = ( ( DIsoB ` K ) ` W )
  assume dihjust.J: |- J = ( ( DIsoC ` K ) ` W )
  assume dihjust.u: |- U = ( ( DVecH ` K ) ` W )
  assume dihjust.s: |- .(+) = ( LSSum ` U )


  assert |- ( ( ( K e. HL /\ W e. H ) /\ ( ( Q e. A /\ -. Q .<_ W ) /\ ( R e. A /\ -. R .<_ W ) /\ X e. B ) /\ ( Q .\/ ( X ./\ W ) ) = ( R .\/ ( X ./\ W ) ) ) -> ( ( J ` Q ) .(+) ( I ` ( X ./\ W ) ) ) = ( ( J ` R ) .(+) ( I ` ( X ./\ W ) ) ) )

  proof
    cK
    chlt
    wcel
    cW
    cH
    wcel
    wa
    #
    cQ
    cA
    wcel
    cQ
    cW
    c.le
    wbr
    wn
    wa
    #
    cR
    cA
    wcel
    cR
    cW
    c.le
    wbr
    wn
    wa
    #
    cX
    cB
    wcel
    #
    w3a
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
    cR
    @5
    c.or
    co
    #
    wceq
    #
    w3a
    #
    cQ
    cJ
    cfv
    @5
    cI
    cfv
    #
    c.po
    co
    #
    cR
    cJ
    cfv
    @10
    c.po
    co
    #
    cA
    cB
    c.po
    cQ
    cR
    cU
    cH
    cI
    cJ
    c.or
    cK
    c.le
    c.an
    cW
    cX
    dihjust.b
    dihjust.l
    dihjust.j
    dihjust.m
    dihjust.a
    dihjust.h
    dihjust.i
    dihjust.J
    dihjust.u
    dihjust.s
    dihjustlem
    @9
    @0
    @2
    @1
    @3
    @7
    @6
    wceq
    @12
    @11
    wss
    @0
    @4
    @8
    simp1
    @0
    @1
    @2
    @3
    @8
    simp22
    @0
    @1
    @2
    @3
    @8
    simp21
    @0
    @1
    @2
    @3
    @8
    simp23
    @9
    @6
    @7
    @0
    @4
    @8
    simp3
    eqcomd
    cA
    cB
    c.po
    cR
    cQ
    cU
    cH
    cI
    cJ
    c.or
    cK
    c.le
    c.an
    cW
    cX
    dihjust.b
    dihjust.l
    dihjust.j
    dihjust.m
    dihjust.a
    dihjust.h
    dihjust.i
    dihjust.J
    dihjust.u
    dihjust.s
    dihjustlem
    syl131anc
    eqssd
end
