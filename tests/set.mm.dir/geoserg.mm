include "cexp.mm"
include "co.mm"
include "cmin.mm"
include "c1.mm"
include "cdiv.mm"
include "cfzo.mm"
include "cv.mm"
include "csu.mm"
include "wceq.mm"
include "cmul.mm"
include "caddc.mm"
include "cfn.mm"
include "wcel.mm"
include "fzofi.mm"
include "a1i.mm"
include "cc.mm"
include "ax-1cn.mm"
include "subcl.mm"
include "sylancr.mm"
include "wa.mm"
include "adantr.mm"
include "cn0.mm"
include "cuz.mm"
include "cfv.mm"
include "elfzouz.mm"
include "eluznn0.mm"
include "syl2an.mm"
include "expcld.mm"
include "fsummulc1.mm"
include "subdid.mm"
include "mulid1d.mm"
include "expp1d.mm"
include "eqcomd.mm"
include "oveq12d.mm"
include "eqtrd.mm"
include "sumeq2dv.mm"
include "oveq2.mm"
include "cfz.mm"
include "elfzuz.mm"
include "telfsumo.mm"
include "3eqtrrd.mm"
include "syl2anc.mm"
include "subcld.mm"
include "fsumcl.mm"
include "cc0.mm"
include "wne.mm"
include "necomd.mm"
include "wb.mm"
include "subeq0.mm"
include "necon3bid.mm"
include "mpbird.mm"
include "divmul3d.mm"

theorem geoserg
  let wph: wff ph
  let cA: class A
  let vk: setvar k
  let cM: class M
  let cN: class N
  let vj: setvar j
  assume geoserg.1: |- ( ph -> A e. CC )
  assume geoserg.2: |- ( ph -> A =/= 1 )
  assume geoserg.3: |- ( ph -> M e. NN0 )
  assume geoserg.4: |- ( ph -> N e. ( ZZ>= ` M ) )

  disjoint A k
  disjoint M k
  disjoint N k
  disjoint k ph
  disjoint j k
  disjoint A j
  disjoint M j
  disjoint N j
  disjoint j ph
  assert |- ( ph -> sum_ k e. ( M ..^ N ) ( A ^ k ) = ( ( ( A ^ M ) - ( A ^ N ) ) / ( 1 - A ) ) )

  proof
    wph
    cA
    cM
    cexp
    co
    #
    cA
    cN
    cexp
    co
    #
    cmin
    co
    #
    c1
    cA
    cmin
    co
    #
    cdiv
    co
    #
    cM
    cN
    cfzo
    co
    #
    cA
    vk
    cv
    #
    cexp
    co
    #
    vk
    csu
    #
    wph
    @4
    @8
    wceq
    @2
    @8
    @3
    cmul
    co
    #
    wceq
    wph
    @9
    @5
    @7
    @3
    cmul
    co
    #
    vk
    csu
    @5
    @7
    cA
    @6
    c1
    caddc
    co
    #
    cexp
    co
    #
    cmin
    co
    #
    vk
    csu
    @2
    wph
    @5
    @7
    @3
    vk
    @5
    cfn
    wcel
    wph
    cM
    cN
    fzofi
    a1i
    #
    wph
    c1
    cc
    wcel
    #
    cA
    cc
    wcel
    #
    @3
    cc
    wcel
    ax-1cn
    geoserg.1
    c1
    cA
    subcl
    sylancr
    #
    wph
    @6
    @5
    wcel
    #
    wa
    #
    cA
    @6
    wph
    @16
    @18
    geoserg.1
    adantr
    #
    wph
    cM
    cn0
    wcel
    #
    @6
    cM
    cuz
    cfv
    #
    wcel
    @6
    cn0
    wcel
    @18
    geoserg.3
    @6
    cM
    cN
    elfzouz
    @6
    cM
    eluznn0
    syl2an
    #
    expcld
    #
    fsummulc1
    wph
    @5
    @10
    @13
    vk
    @19
    @10
    @7
    c1
    cmul
    co
    #
    @7
    cA
    cmul
    co
    #
    cmin
    co
    @13
    @19
    @7
    c1
    cA
    @24
    @15
    @19
    ax-1cn
    a1i
    @20
    subdid
    @19
    @25
    @7
    @26
    @12
    cmin
    @19
    @7
    @24
    mulid1d
    @19
    @12
    @26
    @19
    cA
    @6
    @20
    @23
    expp1d
    eqcomd
    oveq12d
    eqtrd
    sumeq2dv
    wph
    cA
    vj
    cv
    #
    cexp
    co
    @7
    @12
    @0
    vk
    vj
    @1
    cM
    cN
    @27
    @6
    cA
    cexp
    oveq2
    @27
    @11
    cA
    cexp
    oveq2
    @27
    cM
    cA
    cexp
    oveq2
    @27
    cN
    cA
    cexp
    oveq2
    geoserg.4
    wph
    @27
    cM
    cN
    cfz
    co
    wcel
    #
    wa
    cA
    @27
    wph
    @16
    @28
    geoserg.1
    adantr
    wph
    @21
    @27
    @22
    wcel
    @27
    cn0
    wcel
    @28
    geoserg.3
    @27
    cM
    cN
    elfzuz
    @27
    cM
    eluznn0
    syl2an
    expcld
    telfsumo
    3eqtrrd
    wph
    @2
    @8
    @3
    wph
    @0
    @1
    wph
    cA
    cM
    geoserg.1
    geoserg.3
    expcld
    wph
    cA
    cN
    geoserg.1
    wph
    @21
    cN
    @22
    wcel
    cN
    cn0
    wcel
    geoserg.3
    geoserg.4
    cN
    cM
    eluznn0
    syl2anc
    expcld
    subcld
    wph
    @5
    @7
    vk
    @14
    @24
    fsumcl
    @17
    wph
    @3
    cc0
    wne
    c1
    cA
    wne
    wph
    cA
    c1
    geoserg.2
    necomd
    wph
    @3
    cc0
    c1
    cA
    wph
    @15
    @16
    @3
    cc0
    wceq
    c1
    cA
    wceq
    wb
    ax-1cn
    geoserg.1
    c1
    cA
    subeq0
    sylancr
    necon3bid
    mpbird
    divmul3d
    mpbird
    eqcomd
end
