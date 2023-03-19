include "cuspgr.mm"
include "wcel.mm"
include "cword.mm"
include "c1.mm"
include "chash.mm"
include "cfv.mm"
include "cle.mm"
include "wbr.mm"
include "w3a.mm"
include "cv.mm"
include "caddc.mm"
include "co.mm"
include "cpr.mm"
include "crn.mm"
include "cc0.mm"
include "cmin.mm"
include "cfzo.mm"
include "wral.mm"
include "cdm.mm"
include "wa.mm"
include "wf.mm"
include "ccnv.mm"
include "wf1o.mm"
include "cedg.mm"
include "uspgrf1oedg.mm"
include "wceq.mm"
include "ciedg.mm"
include "rneqi.mm"
include "edgval.mm"
include "eqtr4i.mm"
include "a1i.mm"
include "f1oeq3d.mm"
include "mpbird.mm"
include "3ad2ant1.mm"
include "ad2antrr.mm"
include "simpr.mm"
include "wb.mm"
include "fveq2.mm"
include "oveq1.mm"
include "fveq2d.mm"
include "preq12d.mm"
include "eleq1d.mm"
include "adantl.mm"
include "rspcdv.mm"
include "impancom.mm"
include "imp.mm"
include "f1ocnvdm.mm"
include "syl2anc.mm"
include "fmptd.mm"
include "iswrdi.mm"
include "syl.mm"
include "ex.mm"

theorem wlkiswwlks2lem5
  let vx: setvar x
  let cP: class P
  let vi: setvar i
  let cE: class E
  let cF: class F
  let cG: class G
  let cV: class V
  let cI: class I
  assume wlkiswwlks2lem.f: |- F = ( x e. ( 0 ..^ ( ( # ` P ) - 1 ) ) |-> ( `' E ` { ( P ` x ) , ( P ` ( x + 1 ) ) } ) )
  assume wlkiswwlks2lem.e: |- E = ( iEdg ` G )

  disjoint P x
  disjoint E x
  disjoint V x
  disjoint F i
  disjoint G i
  disjoint P i
  disjoint V i
  disjoint i x
  disjoint E i
  disjoint G x
  disjoint I x
  assert |- ( ( G e. USPGraph /\ P e. Word V /\ 1 <_ ( # ` P ) ) -> ( A. i e. ( 0 ..^ ( ( # ` P ) - 1 ) ) { ( P ` i ) , ( P ` ( i + 1 ) ) } e. ran E -> F e. Word dom E ) )

  proof
    cG
    cuspgr
    wcel
    #
    cP
    cV
    cword
    wcel
    #
    c1
    cP
    chash
    cfv
    #
    cle
    wbr
    #
    w3a
    #
    vi
    cv
    #
    cP
    cfv
    #
    @5
    c1
    caddc
    co
    #
    cP
    cfv
    #
    cpr
    #
    cE
    crn
    #
    wcel
    #
    vi
    cc0
    @2
    c1
    cmin
    co
    #
    cfzo
    co
    #
    wral
    #
    cF
    cE
    cdm
    #
    cword
    wcel
    #
    @4
    @14
    wa
    #
    @13
    @15
    cF
    wf
    @16
    @17
    vx
    @13
    vx
    cv
    #
    cP
    cfv
    #
    @18
    c1
    caddc
    co
    #
    cP
    cfv
    #
    cpr
    #
    cE
    ccnv
    cfv
    #
    @15
    cF
    @17
    @18
    @13
    wcel
    #
    wa
    @15
    @10
    cE
    wf1o
    #
    @22
    @10
    wcel
    #
    @23
    @15
    wcel
    @4
    @25
    @14
    @24
    @0
    @1
    @25
    @3
    @0
    @25
    @15
    cG
    cedg
    cfv
    #
    cE
    wf1o
    cE
    cG
    wlkiswwlks2lem.e
    uspgrf1oedg
    @0
    @10
    @27
    @15
    cE
    @10
    @27
    wceq
    @0
    @10
    cG
    ciedg
    cfv
    #
    crn
    @27
    cE
    @28
    wlkiswwlks2lem.e
    rneqi
    cG
    edgval
    eqtr4i
    a1i
    f1oeq3d
    mpbird
    3ad2ant1
    ad2antrr
    @17
    @24
    @26
    @4
    @24
    @14
    @26
    @4
    @24
    wa
    #
    @11
    @26
    vi
    @18
    @13
    @4
    @24
    simpr
    @5
    @18
    wceq
    #
    @11
    @26
    wb
    @29
    @30
    @9
    @22
    @10
    @30
    @6
    @19
    @8
    @21
    @5
    @18
    cP
    fveq2
    @30
    @7
    @20
    cP
    @5
    @18
    c1
    caddc
    oveq1
    fveq2d
    preq12d
    eleq1d
    adantl
    rspcdv
    impancom
    imp
    @15
    @10
    @22
    cE
    f1ocnvdm
    syl2anc
    wlkiswwlks2lem.f
    fmptd
    @15
    @12
    cF
    iswrdi
    syl
    ex
end
