include "chlt.mm"
include "wcel.mm"
include "wa.mm"
include "cv.mm"
include "wbr.mm"
include "wn.mm"
include "cfv.mm"
include "wceq.mm"
include "wi.mm"
include "wral.mm"
include "cid.mm"
include "cres.mm"
include "claut.mm"
include "simp-4l.mm"
include "eqid.mm"
include "ltrnlaut.mm"
include "ad2antrr.mm"
include "simpr.mm"
include "simplll.mm"
include "simpllr.mm"
include "atbase.mm"
include "ad2antlr.mm"
include "ltrnval1.mm"
include "syl112anc.mm"
include "ex.mm"
include "pm2.61.mm"
include "syl.mm"
include "ralimdva.mm"
include "imp.mm"
include "adantr.mm"
include "lauteq.mm"
include "syl31anc.mm"
include "fvresi.mm"
include "adantl.mm"
include "eqtr4d.mm"
include "ralrimiva.mm"
include "wfn.mm"
include "wb.mm"
include "wf1o.mm"
include "ltrn1o.mm"
include "f1ofn.mm"
include "fnresi.mm"
include "eqfnfv.mm"
include "sylancl.mm"
include "mpbird.mm"
include "fveq1.mm"
include "eqeq1d.mm"
include "syl5ibrcom.mm"
include "a1dd.mm"
include "ralrimdva.mm"
include "impbid.mm"

theorem ltrnid
  let cA: class A
  let cB: class B
  let cT: class T
  let cF: class F
  let cH: class H
  let cK: class K
  let c.le: class .<_
  let cW: class W
  let vp: setvar p
  let vx: setvar x
  assume ltrneq.b: |- B = ( Base ` K )
  assume ltrneq.l: |- .<_ = ( le ` K )
  assume ltrneq.a: |- A = ( Atoms ` K )
  assume ltrneq.h: |- H = ( LHyp ` K )
  assume ltrneq.t: |- T = ( ( LTrn ` K ) ` W )

  disjoint A p
  disjoint B p
  disjoint F p
  disjoint H p
  disjoint K p
  disjoint T p
  disjoint W p
  disjoint p x
  disjoint A x
  disjoint B x
  disjoint F x
  disjoint H x
  disjoint K x
  disjoint .<_ x
  disjoint T x
  disjoint W x
  assert |- ( ( ( K e. HL /\ W e. H ) /\ F e. T ) -> ( A. p e. A ( -. p .<_ W -> ( F ` p ) = p ) <-> F = ( _I |` B ) ) )

  proof
    cK
    chlt
    wcel
    #
    cW
    cH
    wcel
    #
    wa
    #
    cF
    cT
    wcel
    #
    wa
    #
    vp
    cv
    #
    cW
    c.le
    wbr
    #
    wn
    #
    @5
    cF
    cfv
    #
    @5
    wceq
    #
    wi
    #
    vp
    cA
    wral
    #
    cF
    cid
    cB
    cres
    #
    wceq
    #
    @4
    @11
    @13
    @4
    @11
    wa
    #
    @13
    vx
    cv
    #
    cF
    cfv
    #
    @15
    @12
    cfv
    #
    wceq
    #
    vx
    cB
    wral
    #
    @14
    @18
    vx
    cB
    @14
    @15
    cB
    wcel
    #
    wa
    #
    @16
    @15
    @17
    @21
    @0
    cF
    cK
    claut
    cfv
    #
    wcel
    #
    @20
    @9
    vp
    cA
    wral
    #
    @16
    @15
    wceq
    @0
    @1
    @3
    @11
    @20
    simp-4l
    @4
    @23
    @11
    @20
    cT
    cF
    cH
    @22
    cK
    chlt
    cW
    ltrneq.h
    @22
    eqid
    #
    ltrneq.t
    ltrnlaut
    ad2antrr
    @14
    @20
    simpr
    @14
    @24
    @20
    @4
    @11
    @24
    @4
    @10
    @9
    vp
    cA
    @4
    @5
    cA
    wcel
    #
    wa
    #
    @6
    @9
    wi
    @10
    @9
    wi
    @27
    @6
    @9
    @27
    @6
    wa
    @2
    @3
    @5
    cB
    wcel
    #
    @6
    @9
    @2
    @3
    @26
    @6
    simplll
    @2
    @3
    @26
    @6
    simpllr
    @26
    @28
    @4
    @6
    cA
    cB
    @5
    cK
    ltrneq.b
    ltrneq.a
    atbase
    #
    ad2antlr
    @27
    @6
    simpr
    cB
    cT
    cF
    cH
    cK
    c.le
    chlt
    cW
    @5
    ltrneq.b
    ltrneq.l
    ltrneq.h
    ltrneq.t
    ltrnval1
    syl112anc
    ex
    @6
    @9
    pm2.61
    syl
    ralimdva
    imp
    adantr
    cA
    cB
    cF
    @22
    cK
    @15
    vp
    ltrneq.b
    ltrneq.a
    @25
    lauteq
    syl31anc
    @20
    @17
    @15
    wceq
    @14
    cB
    @15
    fvresi
    adantl
    eqtr4d
    ralrimiva
    @14
    cF
    cB
    wfn
    #
    @12
    cB
    wfn
    @13
    @19
    wb
    @14
    cB
    cB
    cF
    wf1o
    #
    @30
    @4
    @31
    @11
    cB
    cT
    cF
    cH
    cK
    chlt
    cW
    ltrneq.b
    ltrneq.h
    ltrneq.t
    ltrn1o
    adantr
    cB
    cB
    cF
    f1ofn
    syl
    cB
    fnresi
    vx
    cB
    cF
    @12
    eqfnfv
    sylancl
    mpbird
    ex
    @4
    @13
    @10
    vp
    cA
    @27
    @13
    @9
    @7
    @27
    @9
    @13
    @5
    @12
    cfv
    #
    @5
    wceq
    #
    @27
    @28
    @33
    @26
    @28
    @4
    @29
    adantl
    cB
    @5
    fvresi
    syl
    @13
    @8
    @32
    @5
    @5
    cF
    @12
    fveq1
    eqeq1d
    syl5ibrcom
    a1dd
    ralrimdva
    impbid
end
