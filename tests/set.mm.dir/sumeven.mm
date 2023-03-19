include "c2.mm"
include "cv.mm"
include "csu.mm"
include "cdvds.mm"
include "wbr.mm"
include "c0.mm"
include "csn.mm"
include "cun.mm"
include "wceq.mm"
include "sumeq1.mm"
include "breq2d.mm"
include "cc0.mm"
include "z0even.mm"
include "sum0.mm"
include "breqtrri.mm"
include "a1i.mm"
include "wss.mm"
include "cdif.mm"
include "wcel.mm"
include "wa.mm"
include "csb.mm"
include "caddc.mm"
include "co.mm"
include "cz.mm"
include "w3a.mm"
include "2z.mm"
include "cfn.mm"
include "wi.mm"
include "ssfi.mm"
include "expcom.mm"
include "adantr.mm"
include "mpan9.mm"
include "simpll.mm"
include "ssel.mm"
include "adantl.mm"
include "imp.mm"
include "syl2anc.mm"
include "fsumzcl.mm"
include "wral.mm"
include "eldifi.mm"
include "adantlr.mm"
include "ralrimiva.mm"
include "rspcsbela.mm"
include "3jca.mm"
include "nfcv.mm"
include "nfcsb1v.mm"
include "nfbr.mm"
include "csbeq1a.mm"
include "rspc.mm"
include "syl2imc.mm"
include "a1d.mm"
include "imp32.mm"
include "anim1i.mm"
include "ancomd.mm"
include "dvds2add.mm"
include "sylc.mm"
include "cvv.mm"
include "wnel.mm"
include "vex.mm"
include "wn.mm"
include "eldif.mm"
include "df-nel.mm"
include "biimpri.mm"
include "simplbiim.mm"
include "wo.mm"
include "elun.mm"
include "com12.mm"
include "elsni.mm"
include "eleq1w.mm"
include "syl5ibr.mm"
include "syl.mm"
include "jaoi.mm"
include "syl5bi.mm"
include "fsumsplitsnun.mm"
include "syl121anc.mm"
include "breqtrrd.mm"
include "ex.mm"
include "findcard2d.mm"

theorem sumeven
  let wph: wff ph
  let cA: class A
  let cB: class B
  let vk: setvar k
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  assume sumeven.a: |- ( ph -> A e. Fin )
  assume sumeven.b: |- ( ( ph /\ k e. A ) -> B e. ZZ )
  assume sumeven.e: |- ( ( ph /\ k e. A ) -> 2 || B )

  disjoint A k
  disjoint k ph
  disjoint A x
  disjoint A y
  disjoint A z
  disjoint k x
  disjoint k y
  disjoint k z
  disjoint x y
  disjoint x z
  disjoint y z
  disjoint B x
  disjoint B y
  disjoint B z
  disjoint ph x
  disjoint ph y
  disjoint ph z
  assert |- ( ph -> 2 || sum_ k e. A B )

  proof
    wph
    c2
    vx
    cv
    #
    cB
    vk
    csu
    #
    cdvds
    wbr
    c2
    c0
    cB
    vk
    csu
    #
    cdvds
    wbr
    #
    c2
    vy
    cv
    #
    cB
    vk
    csu
    #
    cdvds
    wbr
    #
    c2
    @4
    vz
    cv
    #
    csn
    #
    cun
    #
    cB
    vk
    csu
    #
    cdvds
    wbr
    #
    c2
    cA
    cB
    vk
    csu
    #
    cdvds
    wbr
    vx
    vy
    vz
    cA
    @0
    c0
    wceq
    @1
    @2
    c2
    cdvds
    @0
    c0
    cB
    vk
    sumeq1
    breq2d
    @0
    @4
    wceq
    @1
    @5
    c2
    cdvds
    @0
    @4
    cB
    vk
    sumeq1
    breq2d
    @0
    @9
    wceq
    @1
    @10
    c2
    cdvds
    @0
    @9
    cB
    vk
    sumeq1
    breq2d
    @0
    cA
    wceq
    @1
    @12
    c2
    cdvds
    @0
    cA
    cB
    vk
    sumeq1
    breq2d
    @3
    wph
    c2
    cc0
    @2
    cdvds
    z0even
    cB
    vk
    sum0
    breqtrri
    a1i
    wph
    @4
    cA
    wss
    #
    @7
    cA
    @4
    cdif
    wcel
    #
    wa
    #
    wa
    #
    @6
    @11
    @16
    @6
    wa
    #
    c2
    @5
    vk
    @7
    cB
    csb
    #
    caddc
    co
    #
    @10
    cdvds
    @17
    c2
    cz
    wcel
    #
    @5
    cz
    wcel
    #
    @18
    cz
    wcel
    #
    w3a
    #
    @6
    c2
    @18
    cdvds
    wbr
    #
    wa
    c2
    @19
    cdvds
    wbr
    @16
    @23
    @6
    @16
    @20
    @21
    @22
    @20
    @16
    2z
    a1i
    @16
    @4
    cB
    vk
    wph
    cA
    cfn
    wcel
    #
    @15
    @4
    cfn
    wcel
    #
    sumeven.a
    @13
    @25
    @26
    wi
    @14
    @25
    @13
    @26
    cA
    @4
    ssfi
    expcom
    adantr
    mpan9
    #
    @16
    vk
    cv
    #
    @4
    wcel
    #
    wa
    wph
    @28
    cA
    wcel
    #
    cB
    cz
    wcel
    #
    wph
    @15
    @29
    simpll
    @16
    @29
    @30
    @15
    @29
    @30
    wi
    #
    wph
    @13
    @32
    @14
    @4
    cA
    @28
    ssel
    adantr
    #
    adantl
    imp
    sumeven.b
    syl2anc
    fsumzcl
    @16
    @7
    cA
    wcel
    #
    @31
    vk
    cA
    wral
    @22
    @15
    @34
    wph
    @14
    @34
    @13
    @7
    cA
    @4
    eldifi
    #
    adantl
    #
    adantl
    @16
    @31
    vk
    cA
    wph
    @30
    @31
    @15
    sumeven.b
    adantlr
    ralrimiva
    vk
    @7
    cA
    cB
    cz
    rspcsbela
    syl2anc
    3jca
    adantr
    @17
    @24
    @6
    @16
    @24
    @6
    wph
    @13
    @14
    @24
    wph
    @14
    @24
    wi
    @13
    @14
    @34
    wph
    c2
    cB
    cdvds
    wbr
    #
    vk
    cA
    wral
    @24
    @35
    wph
    @37
    vk
    cA
    sumeven.e
    ralrimiva
    @37
    @24
    vk
    @7
    cA
    vk
    c2
    @18
    cdvds
    vk
    c2
    nfcv
    vk
    cdvds
    nfcv
    vk
    @7
    cB
    nfcsb1v
    nfbr
    @28
    @7
    wceq
    #
    cB
    @18
    c2
    cdvds
    vk
    @7
    cB
    csbeq1a
    breq2d
    rspc
    syl2imc
    a1d
    imp32
    anim1i
    ancomd
    c2
    @5
    @18
    dvds2add
    sylc
    @16
    @10
    @19
    wceq
    #
    @6
    @16
    @26
    @7
    cvv
    wcel
    #
    @7
    @4
    wnel
    #
    @31
    vk
    @9
    wral
    @39
    @27
    @40
    @16
    vz
    vex
    a1i
    @15
    @41
    wph
    @14
    @41
    @13
    @14
    @34
    @7
    @4
    wcel
    wn
    #
    @41
    @7
    cA
    @4
    eldif
    @41
    @42
    @7
    @4
    df-nel
    biimpri
    simplbiim
    adantl
    adantl
    @16
    @31
    vk
    @9
    @16
    @28
    @9
    wcel
    #
    wa
    wph
    @30
    @31
    wph
    @15
    @43
    simpll
    @16
    @43
    @30
    @15
    @43
    @30
    wi
    wph
    @43
    @29
    @28
    @8
    wcel
    #
    wo
    #
    @15
    @30
    @28
    @4
    @8
    elun
    @45
    @15
    @30
    @29
    @15
    @30
    wi
    #
    @44
    @15
    @29
    @30
    @33
    com12
    @44
    @38
    @46
    @28
    @7
    elsni
    @15
    @30
    @38
    @34
    @36
    vk
    vz
    cA
    eleq1w
    syl5ibr
    syl
    jaoi
    com12
    syl5bi
    adantl
    imp
    sumeven.b
    syl2anc
    ralrimiva
    @4
    cB
    vk
    cvv
    @7
    fsumsplitsnun
    syl121anc
    adantr
    breqtrrd
    ex
    sumeven.a
    findcard2d
end
