include "cli.mm"
include "wbr.mm"
include "cc.mm"
include "wcel.mm"
include "cv.mm"
include "cfv.mm"
include "cmin.mm"
include "co.mm"
include "cabs.mm"
include "clt.mm"
include "cuz.mm"
include "wral.mm"
include "wrex.mm"
include "crp.mm"
include "wa.mm"
include "climcl.mm"
include "adantl.mm"
include "cz.mm"
include "id.mm"
include "cvv.mm"
include "climrel.mm"
include "brrelexi.mm"
include "eqidd.mm"
include "clim.mm"
include "mpbid.mm"
include "simprd.mm"
include "wi.mm"
include "simpr.mm"
include "wb.mm"
include "rexuz3.mm"
include "syl.mm"
include "adantr.mm"
include "mpbird.mm"
include "ralimi.mm"
include "reximi.mm"
include "a1i.mm"
include "mpd.mm"
include "ex.mm"
include "ralimdva.mm"
include "jca.mm"
include "simprl.mm"
include "nfv.mm"
include "nfre1.mm"
include "w3a.mm"
include "uzssz2.mm"
include "sseli.mm"
include "3ad2ant2.mm"
include "simpll.mm"
include "uztrn2.mm"
include "adantll.mm"
include "ffvelrnda.mm"
include "syl2anc.mm"
include "3impia.mm"
include "rspe.mm"
include "3exp.mm"
include "rexlimd.mm"
include "ralimdv.mm"
include "imp.mm"
include "adantrl.mm"
include "fvexi.mm"
include "fexd.mm"
include "impbida.mm"

theorem climuzlem
  let wph: wff ph
  let vx: setvar x
  let cA: class A
  let vj: setvar j
  let vk: setvar k
  let cF: class F
  let cM: class M
  let cZ: class Z
  assume climuzlem.1: |- ( ph -> M e. ZZ )
  assume climuzlem.2: |- Z = ( ZZ>= ` M )
  assume climuzlem.3: |- ( ph -> F : Z --> CC )

  disjoint A j
  disjoint A k
  disjoint A x
  disjoint j k
  disjoint j x
  disjoint k x
  disjoint F j
  disjoint F k
  disjoint F x
  disjoint M j
  disjoint Z j
  disjoint Z k
  disjoint j ph
  disjoint k ph
  disjoint ph x
  assert |- ( ph -> ( F ~~> A <-> ( A e. CC /\ A. x e. RR+ E. j e. Z A. k e. ( ZZ>= ` j ) ( abs ` ( ( F ` k ) - A ) ) < x ) ) )

  proof
    wph
    cF
    cA
    cli
    wbr
    #
    cA
    cc
    wcel
    #
    vk
    cv
    #
    cF
    cfv
    #
    cA
    cmin
    co
    cabs
    cfv
    vx
    cv
    #
    clt
    wbr
    #
    vk
    vj
    cv
    #
    cuz
    cfv
    #
    wral
    #
    vj
    cZ
    wrex
    #
    vx
    crp
    wral
    #
    wa
    #
    wph
    @0
    wa
    #
    @1
    @10
    @0
    @1
    wph
    cA
    cF
    climcl
    adantl
    @12
    @3
    cc
    wcel
    #
    @5
    wa
    #
    vk
    @7
    wral
    #
    vj
    cz
    wrex
    #
    vx
    crp
    wral
    #
    @10
    @0
    @17
    wph
    @0
    @1
    @17
    @0
    @0
    @1
    @17
    wa
    #
    @0
    id
    @0
    vx
    cA
    @3
    vj
    vk
    cF
    cvv
    cF
    cA
    cli
    climrel
    brrelexi
    @0
    @2
    cz
    wcel
    #
    wa
    @3
    eqidd
    clim
    mpbid
    simprd
    adantl
    wph
    @17
    @10
    wi
    @0
    wph
    @16
    @9
    vx
    crp
    wph
    @16
    @9
    wi
    @4
    crp
    wcel
    wph
    @16
    @9
    wph
    @16
    wa
    #
    @15
    vj
    cZ
    wrex
    #
    @9
    @20
    @21
    @16
    wph
    @16
    simpr
    wph
    @21
    @16
    wb
    #
    @16
    wph
    cM
    cz
    wcel
    @22
    climuzlem.1
    @14
    vj
    vk
    cM
    cZ
    climuzlem.2
    rexuz3
    syl
    adantr
    mpbird
    @21
    @9
    wi
    @20
    @15
    @8
    vj
    cZ
    @14
    @5
    vk
    @7
    @13
    @5
    simpr
    ralimi
    reximi
    a1i
    mpd
    ex
    adantr
    ralimdva
    adantr
    mpd
    jca
    wph
    @11
    wa
    #
    @0
    @18
    @23
    @1
    @17
    wph
    @1
    @10
    simprl
    wph
    @10
    @17
    @1
    wph
    @10
    @17
    wph
    @9
    @16
    vx
    crp
    wph
    @8
    @16
    vj
    cZ
    wph
    vj
    nfv
    @15
    vj
    cz
    nfre1
    wph
    @6
    cZ
    wcel
    #
    @8
    @16
    wph
    @24
    @8
    w3a
    @6
    cz
    wcel
    #
    @15
    @16
    @24
    wph
    @25
    @8
    cZ
    cz
    @6
    cM
    cZ
    climuzlem.2
    uzssz2
    sseli
    3ad2ant2
    wph
    @24
    @8
    @15
    wph
    @24
    wa
    #
    @5
    @14
    vk
    @7
    @26
    @2
    @7
    wcel
    #
    wa
    #
    @5
    @14
    @28
    @5
    wa
    @13
    @5
    @28
    @13
    @5
    @28
    wph
    @2
    cZ
    wcel
    #
    @13
    wph
    @24
    @27
    simpll
    @24
    @27
    @29
    wph
    cM
    @2
    @6
    cZ
    climuzlem.2
    uztrn2
    adantll
    wph
    cZ
    cc
    @2
    cF
    climuzlem.3
    ffvelrnda
    syl2anc
    adantr
    @28
    @5
    simpr
    jca
    ex
    ralimdva
    3impia
    @15
    vj
    cz
    rspe
    syl2anc
    3exp
    rexlimd
    ralimdv
    imp
    adantrl
    jca
    wph
    @0
    @18
    wb
    @11
    wph
    vx
    cA
    @3
    vj
    vk
    cF
    cvv
    wph
    cZ
    cc
    cvv
    cF
    climuzlem.3
    cZ
    cvv
    wcel
    wph
    cZ
    cM
    cuz
    climuzlem.2
    fvexi
    a1i
    fexd
    wph
    @19
    wa
    @3
    eqidd
    clim
    adantr
    mpbird
    impbida
end
