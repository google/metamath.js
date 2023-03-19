include "chlt.mm"
include "wcel.mm"
include "wa.mm"
include "wbr.mm"
include "wn.mm"
include "cv.mm"
include "cid.mm"
include "cres.mm"
include "cop.mm"
include "cfv.mm"
include "co.mm"
include "wceq.mm"
include "w3a.mm"
include "ccnv.mm"
include "ccom.mm"
include "cdlemn8.mm"
include "fveq1d.mm"
include "wf.mm"
include "wf1o.mm"
include "simp1.mm"
include "lhpocnel2.mm"
include "3ad2ant1.mm"
include "simp2l.mm"
include "ltrniotacl.mm"
include "syl3anc.mm"
include "ltrn1o.mm"
include "syl2anc.mm"
include "f1ocnv.mm"
include "f1of.mm"
include "3syl.mm"
include "simp2ll.mm"
include "atbase.mm"
include "syl.mm"
include "fvco3.mm"
include "ltrniotacnvval.mm"
include "fveq2d.mm"
include "simp2r.mm"
include "ltrniotaval.mm"
include "eqtrd.mm"
include "3eqtrd.mm"

theorem cdlemn9
  let cA: class A
  let cB: class B
  let cP: class P
  let c.pl: class .+
  let cQ: class Q
  let cR: class R
  let cT: class T
  let cU: class U
  let vg: setvar g
  let vh: setvar h
  let cE: class E
  let cF: class F
  let cG: class G
  let cH: class H
  let cK: class K
  let c.le: class .<_
  let cO: class O
  let cW: class W
  let vs: setvar s
  let vt: setvar t
  let vu: setvar u
  assume cdlemn8.b: |- B = ( Base ` K )
  assume cdlemn8.l: |- .<_ = ( le ` K )
  assume cdlemn8.a: |- A = ( Atoms ` K )
  assume cdlemn8.h: |- H = ( LHyp ` K )
  assume cdlemn8.p: |- P = ( ( oc ` K ) ` W )
  assume cdlemn8.o: |- O = ( h e. T |-> ( _I |` B ) )
  assume cdlemn8.t: |- T = ( ( LTrn ` K ) ` W )
  assume cdlemn8.e: |- E = ( ( TEndo ` K ) ` W )
  assume cdlemn8.u: |- U = ( ( DVecH ` K ) ` W )
  assume cdlemn8.s: |- .+ = ( +g ` U )
  assume cdlemn8.f: |- F = ( iota_ h e. T ( h ` P ) = Q )
  assume cdlemn8.g: |- G = ( iota_ h e. T ( h ` P ) = R )

  disjoint .<_ h
  disjoint A h
  disjoint B h
  disjoint H h
  disjoint K h
  disjoint T h
  disjoint P h
  disjoint Q h
  disjoint W h
  disjoint R h
  disjoint h t
  disjoint h u
  disjoint t u
  disjoint K t
  disjoint K u
  disjoint T t
  disjoint T u
  disjoint E t
  disjoint E u
  disjoint W t
  disjoint W u
  assert |- ( ( ( K e. HL /\ W e. H ) /\ ( ( Q e. A /\ -. Q .<_ W ) /\ ( R e. A /\ -. R .<_ W ) ) /\ ( s e. E /\ g e. T /\ <. G , ( _I |` T ) >. = ( <. ( s ` F ) , s >. .+ <. g , O >. ) ) ) -> ( g ` Q ) = R )

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
    #
    cQ
    cW
    c.le
    wbr
    wn
    #
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
    wa
    #
    vs
    cv
    #
    cE
    wcel
    vg
    cv
    #
    cT
    wcel
    cG
    cid
    cT
    cres
    cop
    cF
    @6
    cfv
    @6
    cop
    @7
    cO
    cop
    c.pl
    co
    wceq
    w3a
    #
    w3a
    #
    cQ
    @7
    cfv
    cQ
    cG
    cF
    ccnv
    #
    ccom
    #
    cfv
    #
    cQ
    @10
    cfv
    #
    cG
    cfv
    #
    cR
    @9
    cQ
    @7
    @11
    cA
    cB
    cP
    c.pl
    cQ
    cR
    cT
    cU
    vg
    vh
    cE
    cF
    cG
    cH
    cK
    c.le
    cO
    cW
    vs
    cdlemn8.b
    cdlemn8.l
    cdlemn8.a
    cdlemn8.h
    cdlemn8.p
    cdlemn8.o
    cdlemn8.t
    cdlemn8.e
    cdlemn8.u
    cdlemn8.s
    cdlemn8.f
    cdlemn8.g
    cdlemn8
    fveq1d
    @9
    cB
    cB
    @10
    wf
    #
    cQ
    cB
    wcel
    #
    @12
    @14
    wceq
    @9
    cB
    cB
    cF
    wf1o
    #
    cB
    cB
    @10
    wf1o
    @15
    @9
    @0
    cF
    cT
    wcel
    #
    @17
    @0
    @5
    @8
    simp1
    #
    @9
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
    @3
    @18
    @19
    @0
    @5
    @20
    @8
    cA
    cP
    cH
    cK
    c.le
    cW
    cdlemn8.l
    cdlemn8.a
    cdlemn8.h
    cdlemn8.p
    lhpocnel2
    3ad2ant1
    #
    @0
    @3
    @4
    @8
    simp2l
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
    cdlemn8.l
    cdlemn8.a
    cdlemn8.h
    cdlemn8.t
    cdlemn8.f
    ltrniotacl
    syl3anc
    cB
    cT
    cF
    cH
    cK
    chlt
    cW
    cdlemn8.b
    cdlemn8.h
    cdlemn8.t
    ltrn1o
    syl2anc
    cB
    cB
    cF
    f1ocnv
    cB
    cB
    @10
    f1of
    3syl
    @9
    @1
    @16
    @1
    @2
    @4
    @0
    @8
    simp2ll
    cA
    cB
    cQ
    cK
    cdlemn8.b
    cdlemn8.a
    atbase
    syl
    cB
    cB
    cQ
    cG
    @10
    fvco3
    syl2anc
    @9
    @14
    cP
    cG
    cfv
    #
    cR
    @9
    @13
    cP
    cG
    @9
    @0
    @20
    @3
    @13
    cP
    wceq
    @19
    @21
    @22
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
    cdlemn8.l
    cdlemn8.a
    cdlemn8.h
    cdlemn8.t
    cdlemn8.f
    ltrniotacnvval
    syl3anc
    fveq2d
    @9
    @0
    @20
    @4
    @23
    cR
    wceq
    @19
    @21
    @0
    @3
    @4
    @8
    simp2r
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
    cdlemn8.l
    cdlemn8.a
    cdlemn8.h
    cdlemn8.t
    cdlemn8.g
    ltrniotaval
    syl3anc
    eqtrd
    3eqtrd
end
