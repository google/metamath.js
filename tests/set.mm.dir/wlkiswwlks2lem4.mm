include "chash.mm"
include "cfv.mm"
include "c1.mm"
include "cmin.mm"
include "co.mm"
include "wceq.mm"
include "cuspgr.mm"
include "wcel.mm"
include "cword.mm"
include "cle.mm"
include "wbr.mm"
include "w3a.mm"
include "cv.mm"
include "caddc.mm"
include "cpr.mm"
include "crn.mm"
include "cc0.mm"
include "cfzo.mm"
include "wral.mm"
include "wi.mm"
include "wlkiswwlks2lem1.mm"
include "3adant1.mm"
include "wa.mm"
include "ccnv.mm"
include "cn0.mm"
include "lencl.mm"
include "3ad2ant2.mm"
include "wlkiswwlks2lem2.mm"
include "sylan.mm"
include "adantr.mm"
include "fveq2d.mm"
include "cdm.mm"
include "wf1o.mm"
include "cedg.mm"
include "uspgrf1oedg.mm"
include "wb.mm"
include "ciedg.mm"
include "rneqi.mm"
include "edgval.mm"
include "eqtr4i.mm"
include "f1oeq3.mm"
include "ax-mp.mm"
include "sylibr.mm"
include "3ad2ant1.mm"
include "f1ocnvfv2.mm"
include "eqtrd.mm"
include "ex.mm"
include "ralimdva.mm"
include "oveq2.mm"
include "raleqdv.mm"
include "imbi2d.mm"
include "syl5ibr.mm"
include "mpcom.mm"

theorem wlkiswwlks2lem4
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
  disjoint I x
  assert |- ( ( G e. USPGraph /\ P e. Word V /\ 1 <_ ( # ` P ) ) -> ( A. i e. ( 0 ..^ ( ( # ` P ) - 1 ) ) { ( P ` i ) , ( P ` ( i + 1 ) ) } e. ran E -> A. i e. ( 0 ..^ ( # ` F ) ) ( E ` ( F ` i ) ) = { ( P ` i ) , ( P ` ( i + 1 ) ) } ) )

  proof
    cF
    chash
    cfv
    #
    cP
    chash
    cfv
    #
    c1
    cmin
    co
    #
    wceq
    #
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
    @1
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
    @8
    c1
    caddc
    co
    cP
    cfv
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
    cfzo
    co
    #
    wral
    #
    @8
    cF
    cfv
    #
    cE
    cfv
    #
    @9
    wceq
    #
    vi
    cc0
    @0
    cfzo
    co
    #
    wral
    #
    wi
    #
    @5
    @6
    @3
    @4
    vx
    cP
    cE
    cF
    cV
    wlkiswwlks2lem.f
    wlkiswwlks2lem1
    3adant1
    @7
    @19
    @3
    @13
    @16
    vi
    @12
    wral
    #
    wi
    @7
    @11
    @16
    vi
    @12
    @7
    @8
    @12
    wcel
    #
    wa
    #
    @11
    @16
    @22
    @11
    wa
    #
    @15
    @9
    cE
    ccnv
    cfv
    #
    cE
    cfv
    #
    @9
    @23
    @14
    @24
    cE
    @22
    @14
    @24
    wceq
    #
    @11
    @7
    @1
    cn0
    wcel
    #
    @21
    @26
    @5
    @4
    @27
    @6
    cV
    cP
    lencl
    3ad2ant2
    vx
    cP
    cE
    cF
    @8
    wlkiswwlks2lem.f
    wlkiswwlks2lem2
    sylan
    adantr
    fveq2d
    @22
    cE
    cdm
    #
    @10
    cE
    wf1o
    #
    @11
    @25
    @9
    wceq
    @7
    @29
    @21
    @4
    @5
    @29
    @6
    @4
    @28
    cG
    cedg
    cfv
    #
    cE
    wf1o
    #
    @29
    cE
    cG
    wlkiswwlks2lem.e
    uspgrf1oedg
    @10
    @30
    wceq
    @29
    @31
    wb
    @10
    cG
    ciedg
    cfv
    #
    crn
    @30
    cE
    @32
    wlkiswwlks2lem.e
    rneqi
    cG
    edgval
    eqtr4i
    @10
    @30
    @28
    cE
    f1oeq3
    ax-mp
    sylibr
    3ad2ant1
    adantr
    @28
    @10
    @9
    cE
    f1ocnvfv2
    sylan
    eqtrd
    ex
    ralimdva
    @3
    @18
    @20
    @13
    @3
    @16
    vi
    @17
    @12
    @0
    @2
    cc0
    cfzo
    oveq2
    raleqdv
    imbi2d
    syl5ibr
    mpcom
end
