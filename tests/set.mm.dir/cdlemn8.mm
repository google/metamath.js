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
include "coass.mm"
include "wf1o.mm"
include "simp1.mm"
include "lhpocnel2.mm"
include "3ad2ant1.mm"
include "simp2l.mm"
include "ltrniotacl.mm"
include "syl3anc.mm"
include "ltrn1o.mm"
include "syl2anc.mm"
include "f1ococnv1.mm"
include "syl.mm"
include "coeq1d.mm"
include "wf.mm"
include "simp32.mm"
include "f1of.mm"
include "fcoi2.mm"
include "3syl.mm"
include "eqtr2d.mm"
include "cdlemn7.mm"
include "simpld.mm"
include "simprd.mm"
include "fveq1d.mm"
include "tendospid.mm"
include "eqtr3d.mm"
include "eqtrd.mm"
include "coeq2d.mm"
include "3eqtr4a.mm"
include "ltrncnv.mm"
include "simp2r.mm"
include "ltrncom.mm"

theorem cdlemn8
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
  assert |- ( ( ( K e. HL /\ W e. H ) /\ ( ( Q e. A /\ -. Q .<_ W ) /\ ( R e. A /\ -. R .<_ W ) ) /\ ( s e. E /\ g e. T /\ <. G , ( _I |` T ) >. = ( <. ( s ` F ) , s >. .+ <. g , O >. ) ) ) -> g = ( G o. `' F ) )

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
    wa
    #
    vs
    cv
    #
    cE
    wcel
    #
    vg
    cv
    #
    cT
    wcel
    #
    cG
    cid
    cT
    cres
    #
    cop
    cF
    @4
    cfv
    #
    @4
    cop
    @6
    cO
    cop
    c.pl
    co
    wceq
    #
    w3a
    #
    w3a
    #
    @6
    cF
    ccnv
    #
    cG
    ccom
    #
    cG
    @13
    ccom
    #
    @12
    @13
    cF
    ccom
    #
    @6
    ccom
    #
    @13
    cF
    @6
    ccom
    #
    ccom
    @6
    @14
    @13
    cF
    @6
    coass
    @12
    @17
    cid
    cB
    cres
    #
    @6
    ccom
    #
    @6
    @12
    @16
    @19
    @6
    @12
    cB
    cB
    cF
    wf1o
    #
    @16
    @19
    wceq
    @12
    @0
    cF
    cT
    wcel
    #
    @21
    @0
    @3
    @11
    simp1
    #
    @12
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
    @22
    @23
    @0
    @3
    @24
    @11
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
    @1
    @2
    @11
    simp2l
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
    #
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
    f1ococnv1
    syl
    coeq1d
    @12
    cB
    cB
    @6
    wf1o
    #
    cB
    cB
    @6
    wf
    @20
    @6
    wceq
    @12
    @0
    @7
    @27
    @23
    @0
    @3
    @5
    @7
    @10
    simp32
    cB
    cT
    @6
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
    @6
    f1of
    cB
    cB
    @6
    fcoi2
    3syl
    eqtr2d
    @12
    cG
    @18
    @13
    @12
    cG
    @9
    @6
    ccom
    #
    @18
    @12
    cG
    @28
    wceq
    #
    @8
    @4
    wceq
    #
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
    cdlemn7
    #
    simpld
    @12
    @9
    cF
    @6
    @12
    cF
    @8
    cfv
    #
    @9
    cF
    @12
    cF
    @8
    @4
    @12
    @29
    @30
    @31
    simprd
    fveq1d
    @12
    @22
    @32
    cF
    wceq
    @26
    cT
    cF
    tendospid
    syl
    eqtr3d
    coeq1d
    eqtrd
    coeq2d
    3eqtr4a
    @12
    @0
    @13
    cT
    wcel
    #
    cG
    cT
    wcel
    #
    @14
    @15
    wceq
    @23
    @12
    @0
    @22
    @33
    @23
    @26
    cT
    cF
    cH
    cK
    cW
    cdlemn8.h
    cdlemn8.t
    ltrncnv
    syl2anc
    @12
    @0
    @24
    @2
    @34
    @23
    @25
    @0
    @1
    @2
    @11
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
    ltrniotacl
    syl3anc
    cT
    @13
    cG
    cH
    cK
    cW
    cdlemn8.h
    cdlemn8.t
    ltrncom
    syl3anc
    eqtrd
end
