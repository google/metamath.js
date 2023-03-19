include "cfn.mm"
include "wcel.mm"
include "c0.mm"
include "wceq.mm"
include "wa.mm"
include "wn.mm"
include "wo.mm"
include "c1.mm"
include "cv.mm"
include "cfz.mm"
include "co.mm"
include "cen.mm"
include "wbr.mm"
include "cn.mm"
include "wrex.mm"
include "exmid.mm"
include "biantrur.mm"
include "andir.mm"
include "bitri.mm"
include "simpl.mm"
include "wi.mm"
include "0fin.mm"
include "eleq1a.mm"
include "ax-mp.mm"
include "ancli.mm"
include "impbii.mm"
include "cn0.mm"
include "wex.mm"
include "rp-isfinite5.mm"
include "df-rex.mm"
include "anbi2i.mm"
include "w3a.mm"
include "cc0.mm"
include "en0.mm"
include "bicomi.mm"
include "ensymb.mm"
include "notbii.mm"
include "elnn0.mm"
include "anbi1i.mm"
include "anbi12i.mm"
include "andi.mm"
include "3anass.mm"
include "orbi12i.mm"
include "sylbb2.mm"
include "simp2.mm"
include "oveq2.mm"
include "fz10.mm"
include "syl6eq.mm"
include "simp3.mm"
include "eqbrtrrd.mm"
include "simp1.mm"
include "pm2.21dd.mm"
include "syl3an2.mm"
include "jaoi.mm"
include "syl.mm"
include "simprr.mm"
include "jca.mm"
include "csdm.mm"
include "chash.mm"
include "cfv.mm"
include "clt.mm"
include "nngt0.mm"
include "hash0.mm"
include "a1i.mm"
include "nnnn0.mm"
include "hashfz1.mm"
include "3brtr4d.mm"
include "wb.mm"
include "fzfi.mm"
include "hashsdom.mm"
include "mp2an.mm"
include "sylib.mm"
include "anim1i.mm"
include "sdomentr.mm"
include "sdomnen.mm"
include "exbii.mm"
include "19.42v.mm"
include "3bitr2ri.mm"

theorem rp-isfinite6
  let cA: class A
  let vn: setvar n

  disjoint A n
  assert |- ( A e. Fin <-> ( A = (/) \/ E. n e. NN ( 1 ... n ) ~~ A ) )

  proof
    cA
    cfn
    wcel
    #
    cA
    c0
    wceq
    #
    @0
    wa
    #
    @1
    wn
    #
    @0
    wa
    #
    wo
    #
    @1
    c1
    vn
    cv
    #
    cfz
    co
    #
    cA
    cen
    wbr
    #
    vn
    cn
    wrex
    #
    wo
    @0
    @1
    @3
    wo
    #
    @0
    wa
    @5
    @10
    @0
    @1
    exmid
    biantrur
    @1
    @3
    @0
    andir
    bitri
    @2
    @1
    @4
    @9
    @2
    @1
    @1
    @0
    simpl
    @1
    @0
    c0
    cfn
    wcel
    #
    @1
    @0
    wi
    0fin
    c0
    cfn
    cA
    eleq1a
    ax-mp
    ancli
    impbii
    @4
    @3
    @6
    cn0
    wcel
    #
    @8
    wa
    #
    vn
    wex
    #
    wa
    #
    @9
    @0
    @14
    @3
    @0
    @8
    vn
    cn0
    wrex
    @14
    cA
    vn
    rp-isfinite5
    @8
    vn
    cn0
    df-rex
    bitri
    anbi2i
    @9
    @6
    cn
    wcel
    #
    @8
    wa
    #
    vn
    wex
    @3
    @13
    wa
    #
    vn
    wex
    @15
    @8
    vn
    cn
    df-rex
    @18
    @17
    vn
    @18
    @17
    @18
    @16
    @8
    @18
    c0
    cA
    cen
    wbr
    #
    wn
    #
    @16
    @8
    w3a
    #
    @20
    @6
    cc0
    wceq
    #
    @8
    w3a
    #
    wo
    #
    @16
    @18
    @20
    @17
    wa
    #
    @20
    @22
    @8
    wa
    #
    wa
    #
    wo
    #
    @24
    @18
    @20
    @17
    @26
    wo
    #
    wa
    @28
    @3
    @20
    @13
    @29
    @1
    @19
    @1
    cA
    c0
    cen
    wbr
    #
    @19
    @30
    @1
    cA
    en0
    #
    bicomi
    cA
    c0
    ensymb
    bitri
    notbii
    @13
    @16
    @22
    wo
    #
    @8
    wa
    @29
    @12
    @32
    @8
    @6
    elnn0
    anbi1i
    @16
    @22
    @8
    andir
    bitri
    anbi12i
    @20
    @17
    @26
    andi
    bitri
    @21
    @25
    @23
    @27
    @20
    @16
    @8
    3anass
    @20
    @22
    @8
    3anass
    orbi12i
    sylbb2
    @21
    @16
    @23
    @20
    @16
    @8
    simp2
    @22
    @20
    @7
    c0
    wceq
    #
    @8
    @16
    @22
    @7
    c1
    cc0
    cfz
    co
    c0
    @6
    cc0
    c1
    cfz
    oveq2
    fz10
    syl6eq
    @20
    @33
    @8
    w3a
    #
    @19
    @16
    @34
    @7
    c0
    cA
    cen
    @20
    @33
    @8
    simp2
    @20
    @33
    @8
    simp3
    eqbrtrrd
    @20
    @33
    @8
    simp1
    pm2.21dd
    syl3an2
    jaoi
    syl
    @3
    @12
    @8
    simprr
    jca
    @17
    @3
    @13
    @17
    c0
    @7
    csdm
    wbr
    #
    @8
    wa
    #
    @3
    @16
    @35
    @8
    @16
    c0
    chash
    cfv
    #
    @7
    chash
    cfv
    #
    clt
    wbr
    #
    @35
    @16
    cc0
    @6
    @37
    @38
    clt
    @6
    nngt0
    @37
    cc0
    wceq
    @16
    hash0
    a1i
    @16
    @12
    @38
    @6
    wceq
    @6
    nnnn0
    #
    @6
    hashfz1
    syl
    3brtr4d
    @11
    @7
    cfn
    wcel
    @39
    @35
    wb
    0fin
    c1
    @6
    fzfi
    c0
    @7
    hashsdom
    mp2an
    sylib
    anim1i
    @36
    @20
    @3
    @36
    c0
    cA
    csdm
    wbr
    @20
    c0
    @7
    cA
    sdomentr
    c0
    cA
    sdomnen
    syl
    @19
    @1
    @19
    @30
    @1
    c0
    cA
    ensymb
    @31
    bitri
    notbii
    sylib
    syl
    @16
    @12
    @8
    @40
    anim1i
    jca
    impbii
    exbii
    @3
    @13
    vn
    19.42v
    3bitr2ri
    bitri
    orbi12i
    bitri
end
