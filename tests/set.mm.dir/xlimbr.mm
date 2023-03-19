include "clsxlim.mm"
include "wbr.mm"
include "cle.mm"
include "cordt.mm"
include "cfv.mm"
include "clm.mm"
include "cxr.mm"
include "cc.mm"
include "cpm.mm"
include "co.mm"
include "wcel.mm"
include "cv.mm"
include "cdm.mm"
include "wa.mm"
include "cuz.mm"
include "wral.mm"
include "cz.mm"
include "wrex.mm"
include "wi.mm"
include "w3a.mm"
include "wb.mm"
include "df-xlim.mm"
include "breqi.mm"
include "a1i.mm"
include "ctopon.mm"
include "letopon.mm"
include "lmbr3.mm"
include "simpr2.mm"
include "eqcomi.mm"
include "raleqi.mm"
include "rexuz3.mm"
include "bicomd.mm"
include "imbi2d.mm"
include "biimpd.mm"
include "ralimdv.mm"
include "syl.mm"
include "imp.mm"
include "sylan2b.mm"
include "3ad2antr3.mm"
include "jca.mm"
include "cvv.mm"
include "cnex.mm"
include "elfvexd.mm"
include "wss.mm"
include "uzsscn2.mm"
include "fpmd.mm"
include "adantr.mm"
include "simprl.mm"
include "biimprd.mm"
include "sylib.mm"
include "adantrl.mm"
include "3jca.mm"
include "impbida.mm"
include "3bitrd.mm"

theorem xlimbr
  let wph: wff ph
  let vu: setvar u
  let cP: class P
  let vj: setvar j
  let vk: setvar k
  let cF: class F
  let cJ: class J
  let cM: class M
  let cZ: class Z
  let vx: setvar x
  assume xlimbr.k: |- F/_ k F
  assume xlimbr.m: |- ( ph -> M e. ZZ )
  assume xlimbr.z: |- Z = ( ZZ>= ` M )
  assume xlimbr.f: |- ( ph -> F : Z --> RR* )
  assume xlimbr.j: |- J = ( ordTop ` <_ )

  disjoint F j
  disjoint F u
  disjoint j u
  disjoint J u
  disjoint M j
  disjoint M u
  disjoint P u
  disjoint Z j
  disjoint Z k
  disjoint j k
  disjoint k u
  disjoint k x
  assert |- ( ph -> ( F ~~>* P <-> ( P e. RR* /\ A. u e. J ( P e. u -> E. j e. Z A. k e. ( ZZ>= ` j ) ( k e. dom F /\ ( F ` k ) e. u ) ) ) ) )

  proof
    wph
    cF
    cP
    clsxlim
    wbr
    #
    cF
    cP
    cle
    cordt
    cfv
    #
    clm
    cfv
    #
    wbr
    #
    cF
    cxr
    cc
    cpm
    co
    wcel
    #
    cP
    cxr
    wcel
    #
    cP
    vu
    cv
    #
    wcel
    #
    vk
    cv
    #
    cF
    cdm
    wcel
    @8
    cF
    cfv
    @6
    wcel
    wa
    #
    vk
    vj
    cv
    cuz
    cfv
    wral
    #
    vj
    cz
    wrex
    #
    wi
    #
    vu
    @1
    wral
    #
    w3a
    #
    @5
    @7
    @10
    vj
    cZ
    wrex
    #
    wi
    #
    vu
    cJ
    wral
    #
    wa
    #
    @0
    @3
    wb
    wph
    cF
    cP
    clsxlim
    @2
    df-xlim
    breqi
    a1i
    wph
    vu
    cP
    vj
    vk
    cF
    @1
    cxr
    xlimbr.k
    @1
    cxr
    ctopon
    cfv
    wcel
    wph
    letopon
    a1i
    #
    lmbr3
    wph
    @14
    @18
    wph
    @14
    wa
    @5
    @17
    wph
    @4
    @5
    @13
    simpr2
    wph
    @4
    @13
    @17
    @5
    @13
    wph
    @12
    vu
    cJ
    wral
    #
    @17
    @12
    vu
    @1
    cJ
    cJ
    @1
    xlimbr.j
    eqcomi
    raleqi
    wph
    @20
    @17
    wph
    cM
    cz
    wcel
    #
    @20
    @17
    wi
    xlimbr.m
    @21
    @12
    @16
    vu
    cJ
    @21
    @12
    @16
    @21
    @11
    @15
    @7
    @21
    @15
    @11
    @9
    vj
    vk
    cM
    cZ
    xlimbr.z
    rexuz3
    bicomd
    imbi2d
    #
    biimpd
    ralimdv
    syl
    imp
    sylan2b
    3ad2antr3
    jca
    wph
    @18
    wa
    @4
    @5
    @13
    wph
    @4
    @18
    wph
    cc
    cxr
    cZ
    cF
    cvv
    cvv
    cc
    cvv
    wcel
    wph
    cnex
    a1i
    wph
    @1
    ctopon
    cxr
    @19
    elfvexd
    cZ
    cc
    wss
    wph
    cM
    cZ
    xlimbr.z
    uzsscn2
    a1i
    xlimbr.f
    fpmd
    adantr
    wph
    @5
    @17
    simprl
    wph
    @17
    @13
    @5
    wph
    @17
    wa
    @20
    @13
    wph
    @17
    @20
    wph
    @21
    @17
    @20
    wi
    xlimbr.m
    @21
    @16
    @12
    vu
    cJ
    @21
    @12
    @16
    @22
    biimprd
    ralimdv
    syl
    imp
    @12
    vu
    cJ
    @1
    xlimbr.j
    raleqi
    sylib
    adantrl
    3jca
    impbida
    3bitrd
end
