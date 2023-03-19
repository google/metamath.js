include "clsp.mm"
include "cfv.mm"
include "crli.mm"
include "wbr.mm"
include "cli.mm"
include "cr.mm"
include "wss.mm"
include "cz.mm"
include "cuz.mm"
include "uzssz.mm"
include "eqsstri.mm"
include "zssre.mm"
include "sstri.mm"
include "a1i.mm"
include "cv.mm"
include "cmin.mm"
include "co.mm"
include "cabs.mm"
include "clt.mm"
include "wral.mm"
include "wrex.mm"
include "crp.mm"
include "cxr.mm"
include "csup.mm"
include "cpnf.mm"
include "wceq.mm"
include "c0.mm"
include "wne.mm"
include "c1.mm"
include "1rp.mm"
include "ne0ii.mm"
include "r19.2z.mm"
include "sylancr.mm"
include "wcel.mm"
include "eluzel2.mm"
include "eleq2s.mm"
include "uzsup.mm"
include "syl.mm"
include "a1d.mm"
include "rexlimiv.mm"
include "rexlimivw.mm"
include "cle.mm"
include "wi.mm"
include "wa.mm"
include "wb.mm"
include "sseli.mm"
include "eluz.mm"
include "syl2an.mm"
include "biimprd.mm"
include "expimpd.mm"
include "imim1d.mm"
include "exp4a.mm"
include "ralimdv2.mm"
include "reximia.mm"
include "ralimi.mm"
include "caurcvgr.mm"
include "wf.mm"
include "cc.mm"
include "ax-resscn.mm"
include "fss.mm"
include "sylancl.mm"
include "rlimclim.mm"
include "mpbid.mm"

theorem caurcvg
  let wph: wff ph
  let vx: setvar x
  let vk: setvar k
  let vm: setvar m
  let cF: class F
  let cM: class M
  let cZ: class Z
  assume caurcvg.1: |- Z = ( ZZ>= ` M )
  assume caurcvg.3: |- ( ph -> F : Z --> RR )
  assume caurcvg.4: |- ( ph -> A. x e. RR+ E. m e. Z A. k e. ( ZZ>= ` m ) ( abs ` ( ( F ` k ) - ( F ` m ) ) ) < x )

  disjoint k m
  disjoint k x
  disjoint F k
  disjoint m x
  disjoint F m
  disjoint F x
  disjoint M m
  disjoint M x
  disjoint k ph
  disjoint m ph
  disjoint ph x
  disjoint Z k
  disjoint Z m
  disjoint Z x
  assert |- ( ph -> F ~~> ( limsup ` F ) )

  proof
    wph
    cF
    cF
    clsp
    cfv
    #
    crli
    wbr
    cF
    @0
    cli
    wbr
    wph
    vx
    cZ
    vm
    vk
    cF
    cZ
    cr
    wss
    wph
    cZ
    cz
    cr
    cZ
    cM
    cuz
    cfv
    #
    cz
    caurcvg.1
    cM
    uzssz
    eqsstri
    #
    zssre
    sstri
    a1i
    caurcvg.3
    wph
    vk
    cv
    #
    cF
    cfv
    vm
    cv
    #
    cF
    cfv
    cmin
    co
    cabs
    cfv
    vx
    cv
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
    vm
    cZ
    wrex
    #
    vx
    crp
    wrex
    #
    cZ
    cxr
    clt
    csup
    cpnf
    wceq
    #
    wph
    crp
    c0
    wne
    @8
    vx
    crp
    wral
    #
    @9
    c1
    crp
    1rp
    ne0ii
    caurcvg.4
    @8
    vx
    crp
    r19.2z
    sylancr
    #
    @8
    @10
    vx
    crp
    @7
    @10
    vm
    cZ
    @4
    cZ
    wcel
    #
    @10
    @7
    @13
    cM
    cz
    wcel
    #
    @10
    @14
    @4
    @1
    cZ
    cM
    @4
    eluzel2
    caurcvg.1
    eleq2s
    #
    cM
    cZ
    caurcvg.1
    uzsup
    syl
    a1d
    rexlimiv
    rexlimivw
    syl
    wph
    @11
    @4
    @3
    cle
    wbr
    #
    @5
    wi
    #
    vk
    cZ
    wral
    #
    vm
    cZ
    wrex
    #
    vx
    crp
    wral
    caurcvg.4
    @8
    @19
    vx
    crp
    @7
    @18
    vm
    cZ
    @13
    @5
    @17
    vk
    @6
    cZ
    @13
    @3
    @6
    wcel
    #
    @5
    wi
    @3
    cZ
    wcel
    #
    @16
    @5
    @13
    @21
    @16
    wa
    @20
    @5
    @13
    @21
    @16
    @20
    @13
    @21
    wa
    @20
    @16
    @13
    @4
    cz
    wcel
    @3
    cz
    wcel
    @20
    @16
    wb
    @21
    cZ
    cz
    @4
    @2
    sseli
    cZ
    cz
    @3
    @2
    sseli
    @4
    @3
    eluz
    syl2an
    biimprd
    expimpd
    imim1d
    exp4a
    ralimdv2
    reximia
    ralimi
    syl
    caurcvgr
    wph
    @0
    cF
    cM
    cZ
    caurcvg.1
    wph
    @9
    @14
    @12
    @8
    @14
    vx
    crp
    @7
    @14
    vm
    cZ
    @13
    @14
    @7
    @15
    a1d
    rexlimiv
    rexlimivw
    syl
    wph
    cZ
    cr
    cF
    wf
    cr
    cc
    wss
    cZ
    cc
    cF
    wf
    caurcvg.3
    ax-resscn
    cZ
    cr
    cc
    cF
    fss
    sylancl
    rlimclim
    mpbid
end
