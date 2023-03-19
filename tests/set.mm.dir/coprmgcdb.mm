include "cn.mm"
include "wcel.mm"
include "wa.mm"
include "cv.mm"
include "cdvds.mm"
include "wbr.mm"
include "c1.mm"
include "wceq.mm"
include "wi.mm"
include "wral.mm"
include "cgcd.mm"
include "co.mm"
include "cz.mm"
include "nnz.mm"
include "gcddvds.mm"
include "syl2an.mm"
include "simpr.mm"
include "gcdnncl.mm"
include "adantr.mm"
include "breq1.mm"
include "anbi12d.mm"
include "eqeq1.mm"
include "imbi12d.mm"
include "rspcv.mm"
include "syl.mm"
include "mpid.mm"
include "mpdan.mm"
include "cle.mm"
include "w3a.mm"
include "simpl.mm"
include "anim1i.mm"
include "ancomd.mm"
include "3anass.mm"
include "sylibr.mm"
include "nndvdslegcd.mm"
include "wb.mm"
include "breq2.mm"
include "nnge1.mm"
include "nnre.mm"
include "1red.mm"
include "letri3d.mm"
include "biimprd.mm"
include "mpan2d.mm"
include "adantl.mm"
include "sylbid.mm"
include "adantll.mm"
include "syld.mm"
include "ralrimiva.mm"
include "ex.mm"
include "impbid.mm"

theorem coprmgcdb
  let cA: class A
  let cB: class B
  let vi: setvar i

  disjoint A i
  disjoint B i
  assert |- ( ( A e. NN /\ B e. NN ) -> ( A. i e. NN ( ( i || A /\ i || B ) -> i = 1 ) <-> ( A gcd B ) = 1 ) )

  proof
    cA
    cn
    wcel
    #
    cB
    cn
    wcel
    #
    wa
    #
    vi
    cv
    #
    cA
    cdvds
    wbr
    #
    @3
    cB
    cdvds
    wbr
    #
    wa
    #
    @3
    c1
    wceq
    #
    wi
    #
    vi
    cn
    wral
    #
    cA
    cB
    cgcd
    co
    #
    c1
    wceq
    #
    @2
    @10
    cA
    cdvds
    wbr
    #
    @10
    cB
    cdvds
    wbr
    #
    wa
    #
    @9
    @11
    wi
    @0
    cA
    cz
    wcel
    cB
    cz
    wcel
    @14
    @1
    cA
    nnz
    cB
    nnz
    cA
    cB
    gcddvds
    syl2an
    @2
    @14
    wa
    #
    @9
    @14
    @11
    @2
    @14
    simpr
    @15
    @10
    cn
    wcel
    #
    @9
    @14
    @11
    wi
    #
    wi
    @2
    @16
    @14
    cA
    cB
    gcdnncl
    adantr
    @8
    @17
    vi
    @10
    cn
    @3
    @10
    wceq
    #
    @6
    @14
    @7
    @11
    @18
    @4
    @12
    @5
    @13
    @3
    @10
    cA
    cdvds
    breq1
    @3
    @10
    cB
    cdvds
    breq1
    anbi12d
    @3
    @10
    c1
    eqeq1
    imbi12d
    rspcv
    syl
    mpid
    mpdan
    @2
    @11
    @9
    @2
    @11
    wa
    #
    @8
    vi
    cn
    @19
    @3
    cn
    wcel
    #
    wa
    #
    @6
    @3
    @10
    cle
    wbr
    #
    @7
    @21
    @20
    @0
    @1
    w3a
    #
    @6
    @22
    wi
    @21
    @20
    @2
    wa
    @23
    @21
    @2
    @20
    @19
    @2
    @20
    @2
    @11
    simpl
    anim1i
    ancomd
    @20
    @0
    @1
    3anass
    sylibr
    @3
    cA
    cB
    nndvdslegcd
    syl
    @11
    @20
    @22
    @7
    wi
    @2
    @11
    @20
    wa
    @22
    @3
    c1
    cle
    wbr
    #
    @7
    @11
    @22
    @24
    wb
    @20
    @10
    c1
    @3
    cle
    breq2
    adantr
    @20
    @24
    @7
    wi
    @11
    @20
    @24
    c1
    @3
    cle
    wbr
    #
    @7
    @3
    nnge1
    @20
    @7
    @24
    @25
    wa
    @20
    @3
    c1
    @3
    nnre
    @20
    1red
    letri3d
    biimprd
    mpan2d
    adantl
    sylbid
    adantll
    syld
    ralrimiva
    ex
    impbid
end
