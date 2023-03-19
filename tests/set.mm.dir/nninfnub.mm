include "cn.mm"
include "wss.mm"
include "cfn.mm"
include "wcel.mm"
include "wn.mm"
include "cv.mm"
include "clt.mm"
include "wbr.mm"
include "crab.mm"
include "c0.mm"
include "wne.mm"
include "wa.mm"
include "wceq.mm"
include "wal.mm"
include "eq0.mm"
include "wral.mm"
include "wi.mm"
include "breq2.mm"
include "elrab.mm"
include "notbii.mm"
include "imnan.mm"
include "sylbb2.mm"
include "alimi.mm"
include "df-ral.mm"
include "sylibr.mm"
include "cle.mm"
include "cr.mm"
include "ssel2.mm"
include "nnred.mm"
include "adantlr.mm"
include "nnre.mm"
include "ad2antlr.mm"
include "lenlt.mm"
include "biimprd.mm"
include "syl2anc.mm"
include "ralimdva.mm"
include "cc0.mm"
include "cfz.mm"
include "co.mm"
include "fzfi.mm"
include "cn0.mm"
include "w3a.mm"
include "nnnn0d.mm"
include "adantr.mm"
include "nnnn0.mm"
include "ad3antlr.mm"
include "simpr.mm"
include "3jca.mm"
include "ex.mm"
include "elfz2nn0.mm"
include "syl6ibr.mm"
include "imp.mm"
include "dfss3.mm"
include "ssfi.mm"
include "sylancr.mm"
include "syld.mm"
include "syl5.mm"
include "syl5bi.mm"
include "necon3bd.mm"
include "an32s.mm"
include "3impa.mm"

theorem nninfnub
  let vx: setvar x
  let cA: class A
  let cB: class B
  let vy: setvar y

  disjoint A x
  disjoint B x
  disjoint A y
  disjoint x y
  disjoint B y
  assert |- ( ( A C_ NN /\ -. A e. Fin /\ B e. NN ) -> { x e. A | B < x } =/= (/) )

  proof
    cA
    cn
    wss
    #
    cA
    cfn
    wcel
    #
    wn
    #
    cB
    cn
    wcel
    #
    cB
    vx
    cv
    #
    clt
    wbr
    #
    vx
    cA
    crab
    #
    c0
    wne
    #
    @0
    @3
    @2
    @7
    @0
    @3
    wa
    #
    @2
    @7
    @8
    @1
    @6
    c0
    @6
    c0
    wceq
    vy
    cv
    #
    @6
    wcel
    #
    wn
    #
    vy
    wal
    #
    @8
    @1
    vy
    @6
    eq0
    @12
    cB
    @9
    clt
    wbr
    #
    wn
    #
    vy
    cA
    wral
    #
    @8
    @1
    @12
    @9
    cA
    wcel
    #
    @14
    wi
    #
    vy
    wal
    @15
    @11
    @17
    vy
    @11
    @16
    @13
    wa
    #
    wn
    @17
    @10
    @18
    @5
    @13
    vx
    @9
    cA
    @4
    @9
    cB
    clt
    breq2
    elrab
    notbii
    @16
    @13
    imnan
    sylbb2
    alimi
    @14
    vy
    cA
    df-ral
    sylibr
    @8
    @15
    @9
    cB
    cle
    wbr
    #
    vy
    cA
    wral
    #
    @1
    @8
    @14
    @19
    vy
    cA
    @8
    @16
    wa
    #
    @9
    cr
    wcel
    #
    cB
    cr
    wcel
    #
    @14
    @19
    wi
    @0
    @16
    @22
    @3
    @0
    @16
    wa
    #
    @9
    cA
    cn
    @9
    ssel2
    #
    nnred
    adantlr
    @3
    @23
    @0
    @16
    cB
    nnre
    ad2antlr
    @22
    @23
    wa
    @19
    @14
    @9
    cB
    lenlt
    biimprd
    syl2anc
    ralimdva
    @8
    @20
    @1
    @8
    @20
    wa
    #
    cc0
    cB
    cfz
    co
    #
    cfn
    wcel
    cA
    @27
    wss
    #
    @1
    cc0
    cB
    fzfi
    @26
    @9
    @27
    wcel
    #
    vy
    cA
    wral
    #
    @28
    @8
    @20
    @30
    @8
    @19
    @29
    vy
    cA
    @21
    @19
    @9
    cn0
    wcel
    #
    cB
    cn0
    wcel
    #
    @19
    w3a
    #
    @29
    @21
    @19
    @33
    @21
    @19
    wa
    @31
    @32
    @19
    @21
    @31
    @19
    @0
    @16
    @31
    @3
    @24
    @9
    @25
    nnnn0d
    adantlr
    adantr
    @3
    @32
    @0
    @16
    @19
    cB
    nnnn0
    ad3antlr
    @21
    @19
    simpr
    3jca
    ex
    @9
    cB
    elfz2nn0
    syl6ibr
    ralimdva
    imp
    vy
    cA
    @27
    dfss3
    sylibr
    @27
    cA
    ssfi
    sylancr
    ex
    syld
    syl5
    syl5bi
    necon3bd
    imp
    an32s
    3impa
end
