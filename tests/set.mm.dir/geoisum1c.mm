include "cc.mm"
include "wcel.mm"
include "cabs.mm"
include "cfv.mm"
include "c1.mm"
include "clt.mm"
include "wbr.mm"
include "w3a.mm"
include "cmul.mm"
include "co.mm"
include "cmin.mm"
include "cdiv.mm"
include "cn.mm"
include "cv.mm"
include "cexp.mm"
include "csu.mm"
include "simp1.mm"
include "simp2.mm"
include "ax-1cn.mm"
include "subcl.mm"
include "sylancr.mm"
include "cc0.mm"
include "wne.mm"
include "simp3.mm"
include "wceq.mm"
include "1re.mm"
include "ltnri.mm"
include "abs1.mm"
include "fveq2.mm"
include "syl5eqr.mm"
include "breq1d.mm"
include "mtbii.mm"
include "necon2ai.mm"
include "syl.mm"
include "wb.mm"
include "wa.mm"
include "subeq0.mm"
include "necon3bid.mm"
include "mpbird.mm"
include "divassd.mm"
include "geoisum1.mm"
include "3adant1.mm"
include "oveq2d.mm"
include "cmpt.mm"
include "nnuz.mm"
include "1zzd.mm"
include "oveq2.mm"
include "eqid.mm"
include "ovex.mm"
include "fvmpt.mm"
include "adantl.mm"
include "cn0.mm"
include "nnnn0.mm"
include "expcl.mm"
include "syl2an.mm"
include "caddc.mm"
include "cseq.mm"
include "cli.mm"
include "cdm.mm"
include "1nn0.mm"
include "a1i.mm"
include "cuz.mm"
include "elnnuz.mm"
include "sylan2br.mm"
include "geolim2.mm"
include "seqex.mm"
include "breldm.mm"
include "isummulc2.mm"
include "3eqtr2rd.mm"

theorem geoisum1c
  let cA: class A
  let cR: class R
  let vk: setvar k
  let vn: setvar n

  disjoint A k
  disjoint R k
  disjoint k n
  disjoint A n
  disjoint R n
  assert |- ( ( A e. CC /\ R e. CC /\ ( abs ` R ) < 1 ) -> sum_ k e. NN ( A x. ( R ^ k ) ) = ( ( A x. R ) / ( 1 - R ) ) )

  proof
    cA
    cc
    wcel
    #
    cR
    cc
    wcel
    #
    cR
    cabs
    cfv
    #
    c1
    clt
    wbr
    #
    w3a
    #
    cA
    cR
    cmul
    co
    c1
    cR
    cmin
    co
    #
    cdiv
    co
    cA
    cR
    @5
    cdiv
    co
    #
    cmul
    co
    cA
    cn
    cR
    vk
    cv
    #
    cexp
    co
    #
    vk
    csu
    #
    cmul
    co
    cn
    cA
    @8
    cmul
    co
    vk
    csu
    @4
    cA
    cR
    @5
    @0
    @1
    @3
    simp1
    #
    @0
    @1
    @3
    simp2
    #
    @4
    c1
    cc
    wcel
    #
    @1
    @5
    cc
    wcel
    ax-1cn
    @11
    c1
    cR
    subcl
    sylancr
    @4
    @5
    cc0
    wne
    #
    c1
    cR
    wne
    #
    @4
    @3
    @14
    @0
    @1
    @3
    simp3
    #
    @3
    c1
    cR
    c1
    cR
    wceq
    #
    c1
    c1
    clt
    wbr
    @3
    c1
    1re
    ltnri
    @16
    c1
    @2
    c1
    clt
    @16
    c1
    c1
    cabs
    cfv
    @2
    abs1
    c1
    cR
    cabs
    fveq2
    syl5eqr
    breq1d
    mtbii
    necon2ai
    syl
    @4
    @12
    @1
    @13
    @14
    wb
    ax-1cn
    @11
    @12
    @1
    wa
    @5
    cc0
    c1
    cR
    c1
    cR
    subeq0
    necon3bid
    sylancr
    mpbird
    divassd
    @4
    @9
    @6
    cA
    cmul
    @1
    @3
    @9
    @6
    wceq
    @0
    cR
    vk
    geoisum1
    3adant1
    oveq2d
    @4
    @8
    cA
    vk
    vn
    cn
    cR
    vn
    cv
    #
    cexp
    co
    #
    cmpt
    #
    c1
    cn
    nnuz
    @4
    1zzd
    @7
    cn
    wcel
    #
    @7
    @19
    cfv
    @8
    wceq
    #
    @4
    vn
    @7
    @18
    @8
    cn
    @19
    @17
    @7
    cR
    cexp
    oveq2
    @19
    eqid
    cR
    @7
    cexp
    ovex
    fvmpt
    adantl
    #
    @4
    @1
    @7
    cn0
    wcel
    @8
    cc
    wcel
    @20
    @11
    @7
    nnnn0
    cR
    @7
    expcl
    syl2an
    @4
    caddc
    @19
    c1
    cseq
    #
    cR
    c1
    cexp
    co
    #
    @5
    cdiv
    co
    #
    cli
    wbr
    @23
    cli
    cdm
    wcel
    @4
    cR
    vk
    @19
    c1
    @11
    @15
    c1
    cn0
    wcel
    @4
    1nn0
    a1i
    @7
    c1
    cuz
    cfv
    wcel
    @4
    @20
    @21
    @7
    elnnuz
    @22
    sylan2br
    geolim2
    @23
    @25
    cli
    caddc
    @19
    c1
    seqex
    @24
    @5
    cdiv
    ovex
    breldm
    syl
    @10
    isummulc2
    3eqtr2rd
end
