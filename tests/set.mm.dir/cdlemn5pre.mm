include "chlt.mm"
include "wcel.mm"
include "wa.mm"
include "wbr.mm"
include "wn.mm"
include "w3a.mm"
include "co.mm"
include "cfv.mm"
include "cid.mm"
include "cres.mm"
include "cop.mm"
include "csn.mm"
include "wceq.mm"
include "simp1.mm"
include "simp22.mm"
include "diclspsn.mm"
include "syl2anc.mm"
include "wss.mm"
include "simp21.mm"
include "cdlemn4a.mm"
include "syl3anc.mm"
include "oveq1d.mm"
include "sseqtr4d.mm"
include "csubg.mm"
include "clss.mm"
include "clmod.mm"
include "dvhlmod.mm"
include "eqid.mm"
include "lsssssubg.mm"
include "syl.mm"
include "diclss.mm"
include "sseldd.mm"
include "simp23.mm"
include "diblss.mm"
include "ctrl.mm"
include "cdlemn2a.mm"
include "lsmless2.mm"
include "sstrd.mm"
include "eqsstrd.mm"

theorem cdlemn5pre
  let cA: class A
  let cB: class B
  let cP: class P
  let c.po: class .(+)
  let cQ: class Q
  let cR: class R
  let cT: class T
  let cU: class U
  let vh: setvar h
  let cE: class E
  let cF: class F
  let cG: class G
  let cH: class H
  let cI: class I
  let cJ: class J
  let c.or: class .\/
  let cK: class K
  let c.le: class .<_
  let cM: class M
  let cN: class N
  let cO: class O
  let cW: class W
  let cX: class X
  assume cdlemn5.b: |- B = ( Base ` K )
  assume cdlemn5.l: |- .<_ = ( le ` K )
  assume cdlemn5.j: |- .\/ = ( join ` K )
  assume cdlemn5.a: |- A = ( Atoms ` K )
  assume cdlemn5.h: |- H = ( LHyp ` K )
  assume cdlemn5.u: |- U = ( ( DVecH ` K ) ` W )
  assume cdlemn5.s: |- .(+) = ( LSSum ` U )
  assume cdlemn5.i: |- I = ( ( DIsoB ` K ) ` W )
  assume cdlemn5.J: |- J = ( ( DIsoC ` K ) ` W )
  assume cdlemn5.p: |- P = ( ( oc ` K ) ` W )
  assume cdlemn5.o: |- O = ( h e. T |-> ( _I |` B ) )
  assume cdlemn5.t: |- T = ( ( LTrn ` K ) ` W )
  assume cdlemn5.e: |- E = ( ( TEndo ` K ) ` W )
  assume cdlemn5.n: |- N = ( LSpan ` U )
  assume cdlemn5.f: |- F = ( iota_ h e. T ( h ` P ) = Q )
  assume cdlemn5.g: |- G = ( iota_ h e. T ( h ` P ) = R )
  assume cdlemn5.m: |- M = ( iota_ h e. T ( h ` Q ) = R )

  disjoint .<_ h
  disjoint A h
  disjoint B h
  disjoint H h
  disjoint K h
  disjoint P h
  disjoint Q h
  disjoint R h
  disjoint T h
  disjoint W h
  assert |- ( ( ( K e. HL /\ W e. H ) /\ ( ( Q e. A /\ -. Q .<_ W ) /\ ( R e. A /\ -. R .<_ W ) /\ ( X e. B /\ X .<_ W ) ) /\ R .<_ ( Q .\/ X ) ) -> ( J ` R ) C_ ( ( J ` Q ) .(+) ( I ` X ) ) )

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
    cX
    cW
    c.le
    wbr
    wa
    #
    w3a
    #
    cR
    cQ
    cX
    c.or
    co
    c.le
    wbr
    #
    w3a
    #
    cR
    cJ
    cfv
    #
    cG
    cid
    cT
    cres
    #
    cop
    csn
    cN
    cfv
    #
    cQ
    cJ
    cfv
    #
    cX
    cI
    cfv
    #
    c.po
    co
    #
    @6
    @0
    @2
    @7
    @9
    wceq
    @0
    @4
    @5
    simp1
    #
    @0
    @1
    @2
    @3
    @5
    simp22
    #
    cA
    cP
    cR
    cT
    cU
    vh
    cG
    cH
    cJ
    cK
    c.le
    cN
    cW
    cdlemn5.l
    cdlemn5.a
    cdlemn5.h
    cdlemn5.p
    cdlemn5.t
    cdlemn5.J
    cdlemn5.u
    cdlemn5.n
    cdlemn5.g
    diclspsn
    syl2anc
    @6
    @9
    @10
    cM
    cO
    cop
    csn
    cN
    cfv
    #
    c.po
    co
    #
    @12
    @6
    @9
    cF
    @8
    cop
    csn
    cN
    cfv
    #
    @15
    c.po
    co
    #
    @16
    @6
    @0
    @1
    @2
    @9
    @18
    wss
    @13
    @0
    @1
    @2
    @3
    @5
    simp21
    #
    @14
    cA
    cB
    cP
    c.po
    cQ
    cR
    cT
    cU
    vh
    cF
    cG
    cH
    cM
    cK
    c.le
    cN
    cO
    cW
    cdlemn5.b
    cdlemn5.l
    cdlemn5.a
    cdlemn5.p
    cdlemn5.h
    cdlemn5.t
    cdlemn5.o
    cdlemn5.u
    cdlemn5.f
    cdlemn5.g
    cdlemn5.m
    cdlemn5.n
    cdlemn5.s
    cdlemn4a
    syl3anc
    @6
    @10
    @17
    @15
    c.po
    @6
    @0
    @1
    @10
    @17
    wceq
    @13
    @19
    cA
    cP
    cQ
    cT
    cU
    vh
    cF
    cH
    cJ
    cK
    c.le
    cN
    cW
    cdlemn5.l
    cdlemn5.a
    cdlemn5.h
    cdlemn5.p
    cdlemn5.t
    cdlemn5.J
    cdlemn5.u
    cdlemn5.n
    cdlemn5.f
    diclspsn
    syl2anc
    oveq1d
    sseqtr4d
    @6
    @10
    cU
    csubg
    cfv
    #
    wcel
    @11
    @20
    wcel
    @15
    @11
    wss
    @16
    @12
    wss
    @6
    cU
    clss
    cfv
    #
    @20
    @10
    @6
    cU
    clmod
    wcel
    @21
    @20
    wss
    @6
    cU
    cH
    cK
    cW
    cdlemn5.h
    cdlemn5.u
    @13
    dvhlmod
    @21
    cU
    @21
    eqid
    #
    lsssssubg
    syl
    #
    @6
    @0
    @1
    @10
    @21
    wcel
    @13
    @19
    cA
    cQ
    @21
    cU
    cH
    cJ
    cK
    c.le
    cW
    cdlemn5.l
    cdlemn5.a
    cdlemn5.h
    cdlemn5.u
    cdlemn5.J
    @22
    diclss
    syl2anc
    sseldd
    @6
    @21
    @20
    @11
    @23
    @6
    @0
    @3
    @11
    @21
    wcel
    @13
    @0
    @1
    @2
    @3
    @5
    simp23
    cB
    @21
    cU
    cH
    cI
    cK
    c.le
    cW
    cX
    cdlemn5.b
    cdlemn5.l
    cdlemn5.h
    cdlemn5.u
    cdlemn5.i
    @22
    diblss
    syl2anc
    sseldd
    cA
    cB
    cQ
    cW
    cK
    ctrl
    cfv
    cfv
    #
    cR
    cT
    cU
    vh
    vh
    cM
    cH
    cI
    c.or
    cK
    c.le
    cN
    cO
    cW
    cX
    cdlemn5.b
    cdlemn5.l
    cdlemn5.j
    cdlemn5.a
    cdlemn5.h
    cdlemn5.t
    @24
    eqid
    cdlemn5.o
    cdlemn5.i
    cdlemn5.u
    cdlemn5.n
    cdlemn5.m
    cdlemn2a
    c.po
    @10
    @15
    @11
    cU
    cdlemn5.s
    lsmless2
    syl3anc
    sstrd
    eqsstrd
end
