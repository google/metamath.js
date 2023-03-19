include "crp.mm"
include "wcel.mm"
include "cr.mm"
include "c1.mm"
include "clt.mm"
include "wbr.mm"
include "w3a.mm"
include "cv.mm"
include "cexp.mm"
include "co.mm"
include "cdiv.mm"
include "cn.mm"
include "wrex.mm"
include "cuz.mm"
include "cfv.mm"
include "wral.mm"
include "expnlbnd.mm"
include "wa.mm"
include "wi.mm"
include "cle.mm"
include "simpl2.mm"
include "simpl3.mm"
include "1re.mm"
include "ltle.mm"
include "sylancr.mm"
include "mpd.mm"
include "simprr.mm"
include "leexp2a.mm"
include "syl3anc.mm"
include "cz.mm"
include "cc0.mm"
include "0red.mm"
include "1red.mm"
include "0lt1.mm"
include "a1i.mm"
include "lttrd.mm"
include "elrpd.mm"
include "nnz.mm"
include "ad2antrl.mm"
include "rpexpcl.mm"
include "syl2anc.mm"
include "eluzelz.mm"
include "ad2antll.mm"
include "lerecd.mm"
include "mpbid.mm"
include "rprecred.mm"
include "simpl1.mm"
include "rpred.mm"
include "lelttr.mm"
include "mpand.mm"
include "anassrs.mm"
include "ralrimdva.mm"
include "reximdva.mm"

theorem expnlbnd2
  let cA: class A
  let cB: class B
  let vj: setvar j
  let vk: setvar k

  disjoint j k
  disjoint A j
  disjoint A k
  disjoint B j
  disjoint B k
  assert |- ( ( A e. RR+ /\ B e. RR /\ 1 < B ) -> E. j e. NN A. k e. ( ZZ>= ` j ) ( 1 / ( B ^ k ) ) < A )

  proof
    cA
    crp
    wcel
    #
    cB
    cr
    wcel
    #
    c1
    cB
    clt
    wbr
    #
    w3a
    #
    c1
    cB
    vj
    cv
    #
    cexp
    co
    #
    cdiv
    co
    #
    cA
    clt
    wbr
    #
    vj
    cn
    wrex
    c1
    cB
    vk
    cv
    #
    cexp
    co
    #
    cdiv
    co
    #
    cA
    clt
    wbr
    #
    vk
    @4
    cuz
    cfv
    #
    wral
    #
    vj
    cn
    wrex
    cA
    cB
    vj
    expnlbnd
    @3
    @7
    @13
    vj
    cn
    @3
    @4
    cn
    wcel
    #
    wa
    @7
    @11
    vk
    @12
    @3
    @14
    @8
    @12
    wcel
    #
    @7
    @11
    wi
    @3
    @14
    @15
    wa
    #
    wa
    #
    @10
    @6
    cle
    wbr
    #
    @7
    @11
    @17
    @5
    @9
    cle
    wbr
    #
    @18
    @17
    @1
    c1
    cB
    cle
    wbr
    #
    @15
    @19
    @0
    @1
    @2
    @16
    simpl2
    #
    @17
    @2
    @20
    @0
    @1
    @2
    @16
    simpl3
    #
    @17
    c1
    cr
    wcel
    @1
    @2
    @20
    wi
    1re
    @21
    c1
    cB
    ltle
    sylancr
    mpd
    @3
    @14
    @15
    simprr
    cB
    @4
    @8
    leexp2a
    syl3anc
    @17
    @5
    @9
    @17
    cB
    crp
    wcel
    #
    @4
    cz
    wcel
    #
    @5
    crp
    wcel
    @17
    cB
    @21
    @17
    cc0
    c1
    cB
    @17
    0red
    @17
    1red
    @21
    cc0
    c1
    clt
    wbr
    @17
    0lt1
    a1i
    @22
    lttrd
    elrpd
    #
    @14
    @24
    @3
    @15
    @4
    nnz
    ad2antrl
    cB
    @4
    rpexpcl
    syl2anc
    #
    @17
    @23
    @8
    cz
    wcel
    #
    @9
    crp
    wcel
    @25
    @15
    @27
    @3
    @14
    @4
    @8
    eluzelz
    ad2antll
    cB
    @8
    rpexpcl
    syl2anc
    #
    lerecd
    mpbid
    @17
    @10
    cr
    wcel
    @6
    cr
    wcel
    cA
    cr
    wcel
    @18
    @7
    wa
    @11
    wi
    @17
    @9
    @28
    rprecred
    @17
    @5
    @26
    rprecred
    @17
    cA
    @0
    @1
    @2
    @16
    simpl1
    rpred
    @10
    @6
    cA
    lelttr
    syl3anc
    mpand
    anassrs
    ralrimdva
    reximdva
    mpd
end
