include "wiso.mm"
include "wss.mm"
include "cima.mm"
include "wceq.mm"
include "cres.mm"
include "wa.mm"
include "wf1o.mm"
include "cv.mm"
include "wbr.mm"
include "cfv.mm"
include "wb.mm"
include "wral.mm"
include "wf1.mm"
include "f1of1.mm"
include "f1ores.mm"
include "expcom.mm"
include "syl5.mm"
include "ssralv.mm"
include "wcel.mm"
include "wi.mm"
include "adantr.mm"
include "fvres.mm"
include "breqan12d.mm"
include "adantll.mm"
include "bibi2d.mm"
include "biimprd.mm"
include "ralimdva.mm"
include "syld.mm"
include "anim12d.mm"
include "df-isom.mm"
include "3imtr4g.mm"
include "impcom.mm"
include "isoeq5.mm"
include "syl5ibrcom.mm"
include "3impia.mm"

theorem isores3
  let cA: class A
  let cB: class B
  let cR: class R
  let cS: class S
  let cH: class H
  let cK: class K
  let cX: class X
  let va: setvar a
  let vb: setvar b


  assert |- ( ( H Isom R , S ( A , B ) /\ K C_ A /\ X = ( H " K ) ) -> ( H |` K ) Isom R , S ( K , X ) )

  proof
    cA
    cB
    cR
    cS
    cH
    wiso
    #
    cK
    cA
    wss
    #
    cX
    cH
    cK
    cima
    #
    wceq
    #
    cK
    cX
    cR
    cS
    cH
    cK
    cres
    #
    wiso
    #
    @0
    @1
    wa
    @5
    @3
    cK
    @2
    cR
    cS
    @4
    wiso
    #
    @1
    @0
    @6
    @1
    cA
    cB
    cH
    wf1o
    #
    va
    cv
    #
    vb
    cv
    #
    cR
    wbr
    #
    @8
    cH
    cfv
    #
    @9
    cH
    cfv
    #
    cS
    wbr
    #
    wb
    #
    vb
    cA
    wral
    #
    va
    cA
    wral
    #
    wa
    cK
    @2
    @4
    wf1o
    #
    @10
    @8
    @4
    cfv
    #
    @9
    @4
    cfv
    #
    cS
    wbr
    #
    wb
    #
    vb
    cK
    wral
    #
    va
    cK
    wral
    #
    wa
    @0
    @6
    @1
    @7
    @17
    @16
    @23
    @7
    cA
    cB
    cH
    wf1
    #
    @1
    @17
    cA
    cB
    cH
    f1of1
    @24
    @1
    @17
    cA
    cB
    cK
    cH
    f1ores
    expcom
    syl5
    @1
    @16
    @15
    va
    cK
    wral
    @23
    @15
    va
    cK
    cA
    ssralv
    @1
    @15
    @22
    va
    cK
    @1
    @8
    cK
    wcel
    #
    wa
    #
    @15
    @14
    vb
    cK
    wral
    #
    @22
    @1
    @15
    @27
    wi
    @25
    @14
    vb
    cK
    cA
    ssralv
    adantr
    @26
    @14
    @21
    vb
    cK
    @26
    @9
    cK
    wcel
    #
    wa
    #
    @21
    @14
    @29
    @20
    @13
    @10
    @25
    @28
    @20
    @13
    wb
    @1
    @25
    @28
    @18
    @11
    @19
    @12
    cS
    @8
    cK
    cH
    fvres
    @9
    cK
    cH
    fvres
    breqan12d
    adantll
    bibi2d
    biimprd
    ralimdva
    syld
    ralimdva
    syld
    anim12d
    va
    vb
    cA
    cB
    cR
    cS
    cH
    df-isom
    va
    vb
    cK
    @2
    cR
    cS
    @4
    df-isom
    3imtr4g
    impcom
    cK
    cX
    @2
    cR
    cS
    @4
    isoeq5
    syl5ibrcom
    3impia
end
