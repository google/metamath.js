include "cuz.mm"
include "cfv.mm"
include "wcel.mm"
include "wa.mm"
include "cfz.mm"
include "co.mm"
include "cprod.mm"
include "c1.mm"
include "caddc.mm"
include "cmul.mm"
include "cc0.mm"
include "clt.mm"
include "wbr.mm"
include "cin.mm"
include "c0.mm"
include "wceq.mm"
include "cz.mm"
include "eluzel2.mm"
include "adantl.mm"
include "zred.mm"
include "ltp1d.mm"
include "fzdisj.mm"
include "syl.mm"
include "cun.mm"
include "w3a.mm"
include "cle.mm"
include "eleq2s.mm"
include "adantr.mm"
include "eluzelz.mm"
include "3jca.mm"
include "eluzle.mm"
include "anim12i.mm"
include "elfz2.mm"
include "sylanbrc.mm"
include "fzsplit.mm"
include "fzfid.mm"
include "cv.mm"
include "cc.mm"
include "elfzuz.mm"
include "syl6eleqr.mm"
include "sylan2.mm"
include "adantlr.mm"
include "fprodsplit.mm"
include "cmin.mm"
include "csb.mm"
include "syl6eleq.mm"
include "fprodm1s.mm"
include "csbied.mm"
include "oveq2d.mm"
include "fprodcl.mm"
include "mul01d.mm"
include "3eqtrd.mm"
include "oveq1d.mm"
include "peano2uzs.mm"
include "uztrn2.mm"
include "syl2an.mm"
include "adantrl.mm"
include "syldan.mm"
include "anassrs.mm"
include "mul02d.mm"

theorem fprodeq0
  let wph: wff ph
  let cA: class A
  let vk: setvar k
  let cK: class K
  let cM: class M
  let cN: class N
  let cZ: class Z
  assume fprodeq0.1: |- Z = ( ZZ>= ` M )
  assume fprodeq0.2: |- ( ph -> N e. Z )
  assume fprodeq0.3: |- ( ( ph /\ k e. Z ) -> A e. CC )
  assume fprodeq0.4: |- ( ( ph /\ k = N ) -> A = 0 )

  disjoint K k
  disjoint M k
  disjoint N k
  disjoint Z k
  disjoint k ph
  assert |- ( ( ph /\ K e. ( ZZ>= ` N ) ) -> prod_ k e. ( M ... K ) A = 0 )

  proof
    wph
    cK
    cN
    cuz
    cfv
    wcel
    #
    wa
    #
    cM
    cK
    cfz
    co
    #
    cA
    vk
    cprod
    cM
    cN
    cfz
    co
    #
    cA
    vk
    cprod
    #
    cN
    c1
    caddc
    co
    #
    cK
    cfz
    co
    #
    cA
    vk
    cprod
    #
    cmul
    co
    cc0
    @7
    cmul
    co
    cc0
    @1
    @3
    @6
    cA
    @2
    vk
    @1
    cN
    @5
    clt
    wbr
    @3
    @6
    cin
    c0
    wceq
    @1
    cN
    @1
    cN
    @0
    cN
    cz
    wcel
    #
    wph
    cN
    cK
    eluzel2
    adantl
    #
    zred
    ltp1d
    cM
    cN
    @5
    cK
    fzdisj
    syl
    @1
    cN
    @2
    wcel
    #
    @2
    @3
    @6
    cun
    wceq
    @1
    cM
    cz
    wcel
    #
    cK
    cz
    wcel
    #
    @8
    w3a
    cM
    cN
    cle
    wbr
    #
    cN
    cK
    cle
    wbr
    #
    wa
    @10
    @1
    @11
    @12
    @8
    wph
    @11
    @0
    wph
    cN
    cZ
    wcel
    #
    @11
    fprodeq0.2
    @11
    cN
    cM
    cuz
    cfv
    #
    cZ
    cM
    cN
    eluzel2
    fprodeq0.1
    eleq2s
    syl
    adantr
    @0
    @12
    wph
    cN
    cK
    eluzelz
    adantl
    @9
    3jca
    wph
    @13
    @0
    @14
    wph
    @15
    @13
    fprodeq0.2
    @13
    cN
    @16
    cZ
    cM
    cN
    eluzle
    fprodeq0.1
    eleq2s
    syl
    cN
    cK
    eluzle
    anim12i
    cN
    cM
    cK
    elfz2
    sylanbrc
    cN
    cM
    cK
    fzsplit
    syl
    @1
    cM
    cK
    fzfid
    wph
    vk
    cv
    #
    @2
    wcel
    #
    cA
    cc
    wcel
    #
    @0
    @18
    wph
    @17
    cZ
    wcel
    #
    @19
    @18
    @17
    @16
    cZ
    @17
    cM
    cK
    elfzuz
    fprodeq0.1
    syl6eleqr
    fprodeq0.3
    sylan2
    adantlr
    fprodsplit
    @1
    @4
    cc0
    @7
    cmul
    wph
    @4
    cc0
    wceq
    @0
    wph
    @4
    cM
    cN
    c1
    cmin
    co
    #
    cfz
    co
    #
    cA
    vk
    cprod
    #
    vk
    cN
    cA
    csb
    #
    cmul
    co
    @23
    cc0
    cmul
    co
    cc0
    wph
    cA
    vk
    cM
    cN
    wph
    cN
    cZ
    @16
    fprodeq0.2
    fprodeq0.1
    syl6eleq
    @17
    @3
    wcel
    #
    wph
    @20
    @19
    @25
    @17
    @16
    cZ
    @17
    cM
    cN
    elfzuz
    fprodeq0.1
    syl6eleqr
    fprodeq0.3
    sylan2
    fprodm1s
    wph
    @24
    cc0
    @23
    cmul
    wph
    vk
    cN
    cA
    cc0
    cZ
    fprodeq0.2
    fprodeq0.4
    csbied
    oveq2d
    wph
    @23
    wph
    @22
    cA
    vk
    wph
    cM
    @21
    fzfid
    @17
    @22
    wcel
    #
    wph
    @20
    @19
    @26
    @17
    @16
    cZ
    @17
    cM
    @21
    elfzuz
    fprodeq0.1
    syl6eleqr
    fprodeq0.3
    sylan2
    fprodcl
    mul01d
    3eqtrd
    adantr
    oveq1d
    @1
    @7
    @1
    @6
    cA
    vk
    @1
    @5
    cK
    fzfid
    wph
    @0
    @17
    @6
    wcel
    #
    @19
    wph
    @0
    @27
    wa
    @20
    @19
    wph
    @27
    @20
    @0
    wph
    @5
    cZ
    wcel
    #
    @17
    @5
    cuz
    cfv
    wcel
    @20
    @27
    wph
    @15
    @28
    fprodeq0.2
    cM
    cN
    cZ
    fprodeq0.1
    peano2uzs
    syl
    @17
    @5
    cK
    elfzuz
    cM
    @17
    @5
    cZ
    fprodeq0.1
    uztrn2
    syl2an
    adantrl
    fprodeq0.3
    syldan
    anassrs
    fprodcl
    mul02d
    3eqtrd
end
