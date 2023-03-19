include "chlt.mm"
include "wcel.mm"
include "wa.mm"
include "wbr.mm"
include "wn.mm"
include "w3a.mm"
include "ccom.mm"
include "cfv.mm"
include "wceq.mm"
include "cbs.mm"
include "wf.mm"
include "wf1o.mm"
include "simp1.mm"
include "lhpocnel2.mm"
include "3ad2ant1.mm"
include "simp2.mm"
include "ltrniotacl.mm"
include "syl3anc.mm"
include "eqid.mm"
include "ltrn1o.mm"
include "syl2anc.mm"
include "f1of.mm"
include "syl.mm"
include "simpld.mm"
include "atbase.mm"
include "fvco3.mm"
include "ltrniotaval.mm"
include "fveq2d.mm"
include "3eqtrd.mm"
include "syld3an2.mm"
include "eqtr4d.mm"
include "wb.mm"
include "ltrnco.mm"
include "ltrneq3.mm"
include "syl121anc.mm"
include "mpbid.mm"

theorem cdlemn3
  let cA: class A
  let cP: class P
  let cQ: class Q
  let cR: class R
  let cT: class T
  let vh: setvar h
  let cF: class F
  let cG: class G
  let cH: class H
  let cJ: class J
  let cK: class K
  let c.le: class .<_
  let cW: class W
  assume cdlemn3.l: |- .<_ = ( le ` K )
  assume cdlemn3.a: |- A = ( Atoms ` K )
  assume cdlemn3.p: |- P = ( ( oc ` K ) ` W )
  assume cdlemn3.h: |- H = ( LHyp ` K )
  assume cdlemn3.t: |- T = ( ( LTrn ` K ) ` W )
  assume cdlemn3.f: |- F = ( iota_ h e. T ( h ` P ) = Q )
  assume cdlemn3.g: |- G = ( iota_ h e. T ( h ` P ) = R )
  assume cdlemn3.j: |- J = ( iota_ h e. T ( h ` Q ) = R )

  disjoint .<_ h
  disjoint A h
  disjoint H h
  disjoint K h
  disjoint P h
  disjoint Q h
  disjoint R h
  disjoint T h
  disjoint W h
  assert |- ( ( ( K e. HL /\ W e. H ) /\ ( Q e. A /\ -. Q .<_ W ) /\ ( R e. A /\ -. R .<_ W ) ) -> ( J o. F ) = G )

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
    cP
    cJ
    cF
    ccom
    #
    cfv
    #
    cP
    cG
    cfv
    #
    wceq
    #
    @4
    cG
    wceq
    #
    @3
    @5
    cR
    @6
    @3
    @5
    cP
    cF
    cfv
    #
    cJ
    cfv
    #
    cQ
    cJ
    cfv
    cR
    @3
    cK
    cbs
    cfv
    #
    @11
    cF
    wf
    #
    cP
    @11
    wcel
    #
    @5
    @10
    wceq
    @3
    @11
    @11
    cF
    wf1o
    #
    @12
    @3
    @0
    cF
    cT
    wcel
    #
    @14
    @0
    @1
    @2
    simp1
    #
    @3
    @0
    cP
    cA
    wcel
    #
    cP
    cW
    c.le
    wbr
    wn
    #
    wa
    #
    @1
    @15
    @16
    @0
    @1
    @19
    @2
    cA
    cP
    cH
    cK
    c.le
    cW
    cdlemn3.l
    cdlemn3.a
    cdlemn3.h
    cdlemn3.p
    lhpocnel2
    3ad2ant1
    #
    @0
    @1
    @2
    simp2
    #
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
    cdlemn3.l
    cdlemn3.a
    cdlemn3.h
    cdlemn3.t
    cdlemn3.f
    ltrniotacl
    syl3anc
    #
    @11
    cT
    cF
    cH
    cK
    chlt
    cW
    @11
    eqid
    #
    cdlemn3.h
    cdlemn3.t
    ltrn1o
    syl2anc
    @11
    @11
    cF
    f1of
    syl
    @3
    @17
    @13
    @3
    @17
    @18
    @20
    simpld
    cA
    @11
    cP
    cK
    @23
    cdlemn3.a
    atbase
    syl
    @11
    @11
    cP
    cJ
    cF
    fvco3
    syl2anc
    @3
    @9
    cQ
    cJ
    @3
    @0
    @19
    @1
    @9
    cQ
    wceq
    @16
    @20
    @21
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
    cdlemn3.l
    cdlemn3.a
    cdlemn3.h
    cdlemn3.t
    cdlemn3.f
    ltrniotaval
    syl3anc
    fveq2d
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
    cdlemn3.l
    cdlemn3.a
    cdlemn3.h
    cdlemn3.t
    cdlemn3.j
    ltrniotaval
    3eqtrd
    @0
    @19
    @1
    @2
    @6
    cR
    wceq
    @20
    cA
    cP
    cR
    cT
    vh
    cG
    cH
    cK
    c.le
    cW
    cdlemn3.l
    cdlemn3.a
    cdlemn3.h
    cdlemn3.t
    cdlemn3.g
    ltrniotaval
    syld3an2
    eqtr4d
    @3
    @0
    @4
    cT
    wcel
    #
    cG
    cT
    wcel
    #
    @19
    @7
    @8
    wb
    @16
    @3
    @0
    cJ
    cT
    wcel
    @15
    @24
    @16
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
    cdlemn3.l
    cdlemn3.a
    cdlemn3.h
    cdlemn3.t
    cdlemn3.j
    ltrniotacl
    @22
    cT
    cJ
    cF
    cH
    cK
    cW
    cdlemn3.h
    cdlemn3.t
    ltrnco
    syl3anc
    @0
    @19
    @1
    @2
    @25
    @20
    cA
    cP
    cR
    cT
    vh
    cG
    cH
    cK
    c.le
    cW
    cdlemn3.l
    cdlemn3.a
    cdlemn3.h
    cdlemn3.t
    cdlemn3.g
    ltrniotacl
    syld3an2
    @20
    cA
    cP
    cT
    @4
    cG
    cH
    cK
    c.le
    cW
    cdlemn3.l
    cdlemn3.a
    cdlemn3.h
    cdlemn3.t
    ltrneq3
    syl121anc
    mpbid
end
