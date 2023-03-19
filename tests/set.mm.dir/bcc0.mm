include "cbcc.mm"
include "co.mm"
include "cc0.mm"
include "wceq.mm"
include "cfallfac.mm"
include "cfa.mm"
include "cfv.mm"
include "cdiv.mm"
include "c1.mm"
include "cmin.mm"
include "cfz.mm"
include "wcel.mm"
include "bccval.mm"
include "eqeq1d.mm"
include "cc.mm"
include "cn0.mm"
include "fallfaccl.mm"
include "syl2anc.mm"
include "cn.mm"
include "faccl.mm"
include "syl.mm"
include "nncnd.mm"
include "wne.mm"
include "facne0.mm"
include "diveq0ad.mm"
include "cv.mm"
include "cprod.mm"
include "fallfacval.mm"
include "wa.mm"
include "cuz.mm"
include "elfzuz3.mm"
include "adantl.mm"
include "nn0uz.mm"
include "elfznn0.mm"
include "ad2antrr.mm"
include "nn0cn.mm"
include "subcld.mm"
include "eqcom.mm"
include "biimpi.mm"
include "subeq0bd.mm"
include "fprodeq0.mm"
include "mpdan.mm"
include "ex.mm"
include "wn.mm"
include "fzfid.mm"
include "nn0cnd.mm"
include "nelne2.mm"
include "necomd.mm"
include "ancoms.mm"
include "adantll.mm"
include "subne0d.mm"
include "fprodn0.mm"
include "necon4bd.mm"
include "impbid.mm"
include "bitr4d.mm"
include "3bitrd.mm"

theorem bcc0
  let wph: wff ph
  let cC: class C
  let cK: class K
  let vc: setvar c
  let vk: setvar k
  assume bccval.c: |- ( ph -> C e. CC )
  assume bccval.k: |- ( ph -> K e. NN0 )


  assert |- ( ph -> ( ( C _Cc K ) = 0 <-> C e. ( 0 ... ( K - 1 ) ) ) )

  proof
    wph
    cC
    cK
    cbcc
    co
    #
    cc0
    wceq
    cC
    cK
    cfallfac
    co
    #
    cK
    cfa
    cfv
    #
    cdiv
    co
    #
    cc0
    wceq
    @1
    cc0
    wceq
    #
    cC
    cc0
    cK
    c1
    cmin
    co
    #
    cfz
    co
    #
    wcel
    #
    wph
    @0
    @3
    cc0
    wph
    cC
    cK
    bccval.c
    bccval.k
    bccval
    eqeq1d
    wph
    @1
    @2
    wph
    cC
    cc
    wcel
    #
    cK
    cn0
    wcel
    #
    @1
    cc
    wcel
    bccval.c
    bccval.k
    cC
    cK
    fallfaccl
    syl2anc
    wph
    @2
    wph
    @9
    @2
    cn
    wcel
    bccval.k
    cK
    faccl
    syl
    nncnd
    wph
    @9
    @2
    cc0
    wne
    bccval.k
    cK
    facne0
    syl
    diveq0ad
    wph
    @4
    @6
    cC
    vk
    cv
    #
    cmin
    co
    #
    vk
    cprod
    #
    cc0
    wceq
    #
    @7
    wph
    @1
    @12
    cc0
    wph
    @8
    @9
    @1
    @12
    wceq
    bccval.c
    bccval.k
    cC
    vk
    cK
    fallfacval
    syl2anc
    eqeq1d
    wph
    @7
    @13
    wph
    @7
    @13
    wph
    @7
    wa
    #
    @5
    cC
    cuz
    cfv
    wcel
    #
    @13
    @7
    @15
    wph
    cC
    cc0
    @5
    elfzuz3
    adantl
    @14
    @11
    vk
    @5
    cc0
    cC
    cn0
    nn0uz
    @7
    cC
    cn0
    wcel
    wph
    cC
    @5
    elfznn0
    adantl
    @14
    @10
    cn0
    wcel
    #
    wa
    cC
    @10
    wph
    @8
    @7
    @16
    bccval.c
    ad2antrr
    @16
    @10
    cc
    wcel
    #
    @14
    @10
    nn0cn
    adantl
    subcld
    @14
    @10
    cC
    wceq
    #
    wa
    cC
    @10
    wph
    @8
    @7
    @18
    bccval.c
    ad2antrr
    @18
    cC
    @10
    wceq
    #
    @14
    @18
    @19
    @10
    cC
    eqcom
    biimpi
    adantl
    subeq0bd
    fprodeq0
    mpdan
    ex
    wph
    @7
    @12
    cc0
    wph
    @7
    wn
    #
    @12
    cc0
    wne
    wph
    @20
    wa
    #
    @6
    @11
    vk
    @21
    cc0
    @5
    fzfid
    @21
    @10
    @6
    wcel
    #
    wa
    #
    cC
    @10
    wph
    @8
    @20
    @22
    bccval.c
    ad2antrr
    #
    @22
    @17
    @21
    @22
    @10
    @10
    @5
    elfznn0
    nn0cnd
    adantl
    #
    subcld
    @23
    cC
    @10
    @24
    @25
    @20
    @22
    cC
    @10
    wne
    #
    wph
    @22
    @20
    @26
    @22
    @20
    wa
    @10
    cC
    @10
    cC
    @6
    nelne2
    necomd
    ancoms
    adantll
    subne0d
    fprodn0
    ex
    necon4bd
    impbid
    bitr4d
    3bitrd
end
