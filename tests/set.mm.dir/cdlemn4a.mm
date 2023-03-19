include "chlt.mm"
include "wcel.mm"
include "wa.mm"
include "wbr.mm"
include "wn.mm"
include "w3a.mm"
include "cid.mm"
include "cres.mm"
include "cop.mm"
include "csn.mm"
include "cfv.mm"
include "cplusg.mm"
include "co.mm"
include "eqid.mm"
include "cdlemn4.mm"
include "sneqd.mm"
include "fveq2d.mm"
include "clmod.mm"
include "cbs.mm"
include "wss.mm"
include "simp1.mm"
include "dvhlmod.mm"
include "ctendo.mm"
include "lhpocnel2.mm"
include "3ad2ant1.mm"
include "simp2.mm"
include "ltrniotacl.mm"
include "syl3anc.mm"
include "tendoidcl.mm"
include "dvhelvbasei.mm"
include "syl12anc.mm"
include "tendo0cl.mm"
include "lspsntri.mm"
include "eqsstrd.mm"

theorem cdlemn4a
  let cA: class A
  let cB: class B
  let cP: class P
  let c.po: class .(+)
  let cQ: class Q
  let cR: class R
  let cT: class T
  let cU: class U
  let vh: setvar h
  let cF: class F
  let cG: class G
  let cH: class H
  let cJ: class J
  let cK: class K
  let c.le: class .<_
  let cN: class N
  let cO: class O
  let cW: class W
  assume cdlemn4.b: |- B = ( Base ` K )
  assume cdlemn4.l: |- .<_ = ( le ` K )
  assume cdlemn4.a: |- A = ( Atoms ` K )
  assume cdlemn4.p: |- P = ( ( oc ` K ) ` W )
  assume cdlemn4.h: |- H = ( LHyp ` K )
  assume cdlemn4.t: |- T = ( ( LTrn ` K ) ` W )
  assume cdlemn4.o: |- O = ( h e. T |-> ( _I |` B ) )
  assume cdlemn4.u: |- U = ( ( DVecH ` K ) ` W )
  assume cdlemn4.f: |- F = ( iota_ h e. T ( h ` P ) = Q )
  assume cdlemn4.g: |- G = ( iota_ h e. T ( h ` P ) = R )
  assume cdlemn4.j: |- J = ( iota_ h e. T ( h ` Q ) = R )
  assume cdlemn4a.n: |- N = ( LSpan ` U )
  assume cdlemn4a.s: |- .(+) = ( LSSum ` U )

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
  assert |- ( ( ( K e. HL /\ W e. H ) /\ ( Q e. A /\ -. Q .<_ W ) /\ ( R e. A /\ -. R .<_ W ) ) -> ( N ` { <. G , ( _I |` T ) >. } ) C_ ( ( N ` { <. F , ( _I |` T ) >. } ) .(+) ( N ` { <. J , O >. } ) ) )

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
    w3a
    #
    cG
    cid
    cT
    cres
    #
    cop
    #
    csn
    #
    cN
    cfv
    cF
    @4
    cop
    #
    cJ
    cO
    cop
    #
    cU
    cplusg
    cfv
    #
    co
    #
    csn
    #
    cN
    cfv
    #
    @7
    csn
    cN
    cfv
    @8
    csn
    cN
    cfv
    c.po
    co
    #
    @3
    @6
    @11
    cN
    @3
    @5
    @10
    cA
    cB
    cP
    @9
    cQ
    cR
    cT
    cU
    vh
    cF
    cG
    cH
    cJ
    cK
    c.le
    cO
    cW
    cdlemn4.b
    cdlemn4.l
    cdlemn4.a
    cdlemn4.p
    cdlemn4.h
    cdlemn4.t
    cdlemn4.o
    cdlemn4.u
    cdlemn4.f
    cdlemn4.g
    cdlemn4.j
    @9
    eqid
    #
    cdlemn4
    sneqd
    fveq2d
    @3
    cU
    clmod
    wcel
    @7
    cU
    cbs
    cfv
    #
    wcel
    #
    @8
    @15
    wcel
    #
    @12
    @13
    wss
    @3
    cU
    cH
    cK
    cW
    cdlemn4.h
    cdlemn4.u
    @0
    @1
    @2
    simp1
    #
    dvhlmod
    @3
    @0
    cF
    cT
    wcel
    #
    @4
    cW
    cK
    ctendo
    cfv
    cfv
    #
    wcel
    #
    @16
    @18
    @3
    @0
    cP
    cA
    wcel
    cP
    cW
    c.le
    wbr
    wn
    wa
    #
    @1
    @19
    @18
    @0
    @1
    @22
    @2
    cA
    cP
    cH
    cK
    c.le
    cW
    cdlemn4.l
    cdlemn4.a
    cdlemn4.h
    cdlemn4.p
    lhpocnel2
    3ad2ant1
    @0
    @1
    @2
    simp2
    cA
    cP
    cQ
    cT
    vh
    cF
    cH
    cK
    c.le
    cW
    cdlemn4.l
    cdlemn4.a
    cdlemn4.h
    cdlemn4.t
    cdlemn4.f
    ltrniotacl
    syl3anc
    @0
    @1
    @21
    @2
    cT
    @20
    cH
    cK
    cW
    cdlemn4.h
    cdlemn4.t
    @20
    eqid
    #
    tendoidcl
    3ad2ant1
    @4
    cT
    cU
    @20
    cF
    cH
    cK
    @15
    cW
    chlt
    cdlemn4.h
    cdlemn4.t
    @23
    cdlemn4.u
    @15
    eqid
    #
    dvhelvbasei
    syl12anc
    @3
    @0
    cJ
    cT
    wcel
    cO
    @20
    wcel
    #
    @17
    @18
    cA
    cQ
    cR
    cT
    vh
    cJ
    cH
    cK
    c.le
    cW
    cdlemn4.l
    cdlemn4.a
    cdlemn4.h
    cdlemn4.t
    cdlemn4.j
    ltrniotacl
    @0
    @1
    @25
    @2
    cB
    cT
    vh
    @20
    cH
    cK
    cO
    cW
    cdlemn4.b
    cdlemn4.h
    cdlemn4.t
    @23
    cdlemn4.o
    tendo0cl
    3ad2ant1
    cO
    cT
    cU
    @20
    cJ
    cH
    cK
    @15
    cW
    chlt
    cdlemn4.h
    cdlemn4.t
    @23
    cdlemn4.u
    @24
    dvhelvbasei
    syl12anc
    @9
    c.po
    cN
    @15
    cU
    @7
    @8
    @24
    @14
    cdlemn4a.n
    cdlemn4a.s
    lspsntri
    syl3anc
    eqsstrd
end
