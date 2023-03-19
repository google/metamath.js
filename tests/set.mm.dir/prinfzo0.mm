include "cz.mm"
include "wcel.mm"
include "csn.mm"
include "c1.mm"
include "caddc.mm"
include "co.mm"
include "cfzo.mm"
include "cin.mm"
include "c0.mm"
include "wceq.mm"
include "cpr.mm"
include "wn.mm"
include "cuz.mm"
include "cfv.mm"
include "clt.mm"
include "wbr.mm"
include "w3o.mm"
include "cfz.mm"
include "elfz3.mm"
include "fznuz.mm"
include "syl.mm"
include "3mix1d.mm"
include "w3a.mm"
include "3ianor.mm"
include "elfzo2.mm"
include "xchnxbir.mm"
include "sylibr.mm"
include "incom.mm"
include "eqeq1i.mm"
include "disjsn.mm"
include "bitri.mm"
include "fzonel.mm"
include "a1i.mm"
include "cun.mm"
include "wa.mm"
include "df-pr.mm"
include "ineq1i.mm"
include "undisj1.mm"
include "bitr4i.mm"
include "sylanbrc.mm"

theorem prinfzo0
  let cM: class M
  let cN: class N


  assert |- ( M e. ZZ -> ( { M , N } i^i ( ( M + 1 ) ..^ N ) ) = (/) )

  proof
    cM
    cz
    wcel
    #
    cM
    csn
    #
    cM
    c1
    caddc
    co
    #
    cN
    cfzo
    co
    #
    cin
    #
    c0
    wceq
    #
    cN
    csn
    #
    @3
    cin
    #
    c0
    wceq
    #
    cM
    cN
    cpr
    #
    @3
    cin
    #
    c0
    wceq
    #
    @0
    cM
    @3
    wcel
    #
    wn
    #
    @5
    @0
    cM
    @2
    cuz
    cfv
    wcel
    #
    wn
    #
    cN
    cz
    wcel
    #
    wn
    #
    cM
    cN
    clt
    wbr
    #
    wn
    #
    w3o
    #
    @13
    @0
    @15
    @17
    @19
    @0
    cM
    cM
    cM
    cfz
    co
    wcel
    @15
    cM
    elfz3
    cM
    cM
    cM
    fznuz
    syl
    3mix1d
    @14
    @16
    @18
    w3a
    @20
    @12
    @14
    @16
    @18
    3ianor
    cM
    @2
    cN
    elfzo2
    xchnxbir
    sylibr
    @5
    @3
    @1
    cin
    #
    c0
    wceq
    @13
    @4
    @21
    c0
    @1
    @3
    incom
    eqeq1i
    @3
    cM
    disjsn
    bitri
    sylibr
    @0
    cN
    @3
    wcel
    wn
    #
    @8
    @22
    @0
    @2
    cN
    fzonel
    a1i
    @8
    @3
    @6
    cin
    #
    c0
    wceq
    @22
    @7
    @23
    c0
    @6
    @3
    incom
    eqeq1i
    @3
    cN
    disjsn
    bitri
    sylibr
    @11
    @1
    @6
    cun
    #
    @3
    cin
    #
    c0
    wceq
    @5
    @8
    wa
    @10
    @25
    c0
    @9
    @24
    @3
    cM
    cN
    df-pr
    ineq1i
    eqeq1i
    @1
    @6
    @3
    undisj1
    bitr4i
    sylanbrc
end
