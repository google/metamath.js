include "ctopon.mm"
include "cfv.mm"
include "wcel.mm"
include "cfil.mm"
include "wa.mm"
include "cfcls.mm"
include "co.mm"
include "cv.mm"
include "ccl.mm"
include "wral.mm"
include "cin.mm"
include "c0.mm"
include "wne.mm"
include "wi.mm"
include "isfcls2.mm"
include "wrex.mm"
include "filn0.mm"
include "adantl.mm"
include "r19.2z.mm"
include "ex.mm"
include "syl.mm"
include "cuni.mm"
include "ctop.mm"
include "wss.mm"
include "topontop.mm"
include "ad2antrr.mm"
include "filelss.mm"
include "adantll.mm"
include "wceq.mm"
include "toponuni.mm"
include "sseqtrd.mm"
include "eqid.mm"
include "clsss3.mm"
include "syl2anc.mm"
include "sseqtr4d.mm"
include "sseld.mm"
include "rexlimdva.mm"
include "syld.mm"
include "pm4.71rd.mm"
include "wb.mm"
include "ad3antrrr.mm"
include "adantlr.mm"
include "simplr.mm"
include "eleqtrd.mm"
include "elcls.mm"
include "syl3anc.mm"
include "ralbidva.mm"
include "ralcom.mm"
include "r19.21v.mm"
include "ralbii.mm"
include "bitri.mm"
include "syl6bb.mm"
include "pm5.32da.mm"
include "3bitrd.mm"

theorem fclsopn
  let cA: class A
  let vo: setvar o
  let cF: class F
  let cJ: class J
  let cX: class X
  let vs: setvar s
  let cU: class U
  let cS: class S

  disjoint o s
  disjoint A o
  disjoint A s
  disjoint F o
  disjoint F s
  disjoint J o
  disjoint J s
  disjoint X o
  disjoint X s
  disjoint U o
  disjoint U s
  disjoint S s
  assert |- ( ( J e. ( TopOn ` X ) /\ F e. ( Fil ` X ) ) -> ( A e. ( J fClus F ) <-> ( A e. X /\ A. o e. J ( A e. o -> A. s e. F ( o i^i s ) =/= (/) ) ) ) )

  proof
    cJ
    cX
    ctopon
    cfv
    wcel
    #
    cF
    cX
    cfil
    cfv
    wcel
    #
    wa
    #
    cA
    cJ
    cF
    cfcls
    co
    wcel
    cA
    vs
    cv
    #
    cJ
    ccl
    cfv
    cfv
    #
    wcel
    #
    vs
    cF
    wral
    #
    cA
    cX
    wcel
    #
    @6
    wa
    @7
    cA
    vo
    cv
    #
    wcel
    #
    @8
    @3
    cin
    c0
    wne
    #
    vs
    cF
    wral
    wi
    #
    vo
    cJ
    wral
    #
    wa
    cA
    cF
    cJ
    cX
    vs
    isfcls2
    @2
    @6
    @7
    @2
    @6
    @5
    vs
    cF
    wrex
    #
    @7
    @2
    cF
    c0
    wne
    #
    @6
    @13
    wi
    @1
    @14
    @0
    cF
    cX
    filn0
    adantl
    @14
    @6
    @13
    @5
    vs
    cF
    r19.2z
    ex
    syl
    @2
    @5
    @7
    vs
    cF
    @2
    @3
    cF
    wcel
    #
    wa
    #
    @4
    cX
    cA
    @16
    @4
    cJ
    cuni
    #
    cX
    @16
    cJ
    ctop
    wcel
    #
    @3
    @17
    wss
    #
    @4
    @17
    wss
    @0
    @18
    @1
    @15
    cX
    cJ
    topontop
    #
    ad2antrr
    @16
    @3
    cX
    @17
    @1
    @15
    @3
    cX
    wss
    @0
    @3
    cF
    cX
    filelss
    adantll
    @0
    cX
    @17
    wceq
    #
    @1
    @15
    cX
    cJ
    toponuni
    #
    ad2antrr
    #
    sseqtrd
    #
    @3
    cJ
    @17
    @17
    eqid
    #
    clsss3
    syl2anc
    @23
    sseqtr4d
    sseld
    rexlimdva
    syld
    pm4.71rd
    @2
    @7
    @6
    @12
    @2
    @7
    wa
    #
    @6
    @9
    @10
    wi
    #
    vo
    cJ
    wral
    #
    vs
    cF
    wral
    #
    @12
    @26
    @5
    @28
    vs
    cF
    @26
    @15
    wa
    #
    @18
    @19
    cA
    @17
    wcel
    @5
    @28
    wb
    @0
    @18
    @1
    @7
    @15
    @20
    ad3antrrr
    @2
    @15
    @19
    @7
    @24
    adantlr
    @30
    cA
    cX
    @17
    @2
    @7
    @15
    simplr
    @0
    @21
    @1
    @7
    @15
    @22
    ad3antrrr
    eleqtrd
    vo
    cA
    @3
    cJ
    @17
    @25
    elcls
    syl3anc
    ralbidva
    @29
    @27
    vs
    cF
    wral
    #
    vo
    cJ
    wral
    @12
    @27
    vs
    vo
    cF
    cJ
    ralcom
    @31
    @11
    vo
    cJ
    @9
    @10
    vs
    cF
    r19.21v
    ralbii
    bitri
    syl6bb
    pm5.32da
    3bitrd
end
