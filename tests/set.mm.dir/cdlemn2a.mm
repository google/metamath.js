include "chlt.mm"
include "wcel.mm"
include "wa.mm"
include "wbr.mm"
include "wn.mm"
include "w3a.mm"
include "co.mm"
include "cop.mm"
include "csn.mm"
include "cfv.mm"
include "wceq.mm"
include "simp1.mm"
include "simp21.mm"
include "simp22.mm"
include "ltrniotacl.mm"
include "syl3anc.mm"
include "dib1dim2.mm"
include "syl2anc.mm"
include "wss.mm"
include "cdlemn2.mm"
include "wb.mm"
include "trlcl.mm"
include "trlle.mm"
include "simp23.mm"
include "dibord.mm"
include "syl121anc.mm"
include "mpbird.mm"
include "eqsstr3d.mm"

theorem cdlemn2a
  let cA: class A
  let cB: class B
  let cQ: class Q
  let cR: class R
  let cS: class S
  let cT: class T
  let cU: class U
  let vf: setvar f
  let vh: setvar h
  let cF: class F
  let cH: class H
  let cI: class I
  let c.or: class .\/
  let cK: class K
  let c.le: class .<_
  let cN: class N
  let cO: class O
  let cW: class W
  let cX: class X
  assume cdlemn2a.b: |- B = ( Base ` K )
  assume cdlemn2a.l: |- .<_ = ( le ` K )
  assume cdlemn2a.j: |- .\/ = ( join ` K )
  assume cdlemn2a.a: |- A = ( Atoms ` K )
  assume cdlemn2a.h: |- H = ( LHyp ` K )
  assume cdlemn2a.t: |- T = ( ( LTrn ` K ) ` W )
  assume cdlemn2a.r: |- R = ( ( trL ` K ) ` W )
  assume cdlemn2a.o: |- O = ( f e. T |-> ( _I |` B ) )
  assume cdlemn2a.i: |- I = ( ( DIsoB ` K ) ` W )
  assume cdlemn2a.u: |- U = ( ( DVecH ` K ) ` W )
  assume cdlemn2a.n: |- N = ( LSpan ` U )
  assume cdlemn2a.f: |- F = ( iota_ h e. T ( h ` Q ) = S )

  disjoint .<_ h
  disjoint A h
  disjoint B f
  disjoint H h
  disjoint K f
  disjoint K h
  disjoint Q h
  disjoint S h
  disjoint T f
  disjoint T h
  disjoint W f
  disjoint W h
  assert |- ( ( ( K e. HL /\ W e. H ) /\ ( ( Q e. A /\ -. Q .<_ W ) /\ ( S e. A /\ -. S .<_ W ) /\ ( X e. B /\ X .<_ W ) ) /\ S .<_ ( Q .\/ X ) ) -> ( N ` { <. F , O >. } ) C_ ( I ` X ) )

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
    cS
    cA
    wcel
    cS
    cW
    c.le
    wbr
    wn
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
    w3a
    #
    cS
    cQ
    cX
    c.or
    co
    c.le
    wbr
    #
    w3a
    #
    cF
    cO
    cop
    csn
    cN
    cfv
    #
    cF
    cR
    cfv
    #
    cI
    cfv
    #
    cX
    cI
    cfv
    #
    @6
    @0
    cF
    cT
    wcel
    #
    @9
    @7
    wceq
    @0
    @4
    @5
    simp1
    #
    @6
    @0
    @1
    @2
    @11
    @12
    @0
    @1
    @2
    @3
    @5
    simp21
    @0
    @1
    @2
    @3
    @5
    simp22
    cA
    cQ
    cS
    cT
    vh
    cF
    cH
    cK
    c.le
    cW
    cdlemn2a.l
    cdlemn2a.a
    cdlemn2a.h
    cdlemn2a.t
    cdlemn2a.f
    ltrniotacl
    syl3anc
    #
    cB
    cR
    cT
    cU
    vf
    cF
    cH
    cI
    cK
    cN
    cO
    cW
    cdlemn2a.b
    cdlemn2a.h
    cdlemn2a.t
    cdlemn2a.r
    cdlemn2a.o
    cdlemn2a.u
    cdlemn2a.i
    cdlemn2a.n
    dib1dim2
    syl2anc
    @6
    @9
    @10
    wss
    #
    @8
    cX
    c.le
    wbr
    #
    cA
    cB
    cQ
    cR
    cS
    cT
    vh
    cF
    cH
    c.or
    cK
    c.le
    cW
    cX
    cdlemn2a.b
    cdlemn2a.l
    cdlemn2a.j
    cdlemn2a.a
    cdlemn2a.h
    cdlemn2a.t
    cdlemn2a.r
    cdlemn2a.f
    cdlemn2
    @6
    @0
    @8
    cB
    wcel
    #
    @8
    cW
    c.le
    wbr
    #
    @3
    @14
    @15
    wb
    @12
    @6
    @0
    @11
    @16
    @12
    @13
    cB
    cR
    cT
    cF
    cH
    cK
    cW
    cdlemn2a.b
    cdlemn2a.h
    cdlemn2a.t
    cdlemn2a.r
    trlcl
    syl2anc
    @6
    @0
    @11
    @17
    @12
    @13
    cR
    cT
    cF
    cH
    cK
    c.le
    cW
    cdlemn2a.l
    cdlemn2a.h
    cdlemn2a.t
    cdlemn2a.r
    trlle
    syl2anc
    @0
    @1
    @2
    @3
    @5
    simp23
    cB
    cH
    cI
    cK
    c.le
    cW
    @8
    cX
    cdlemn2a.b
    cdlemn2a.l
    cdlemn2a.h
    cdlemn2a.i
    dibord
    syl121anc
    mpbird
    eqsstr3d
end
