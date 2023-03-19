include "cv.mm"
include "csu.mm"
include "clt.mm"
include "wbr.mm"
include "cpw.mm"
include "cfn.mm"
include "cin.mm"
include "wrex.mm"
include "cfz.mm"
include "co.mm"
include "cvv.mm"
include "wcel.mm"
include "cuz.mm"
include "cfv.mm"
include "fvex.mm"
include "eqeltri.mm"
include "a1i.mm"
include "sge0gtfsumgt.mm"
include "w3a.mm"
include "wss.mm"
include "cz.mm"
include "3ad2ant1.mm"
include "elpwinss.mm"
include "3ad2ant2.mm"
include "elinel2.mm"
include "uzfissfz.mm"
include "wi.mm"
include "wa.mm"
include "cr.mm"
include "ad2antrr.mm"
include "nfv.mm"
include "nfan.mm"
include "fzfid.mm"
include "simpr.mm"
include "ssfid.mm"
include "simpll.mm"
include "sselda.mm"
include "cc0.mm"
include "cpnf.mm"
include "cico.mm"
include "rge0ssre.mm"
include "fzssuz.mm"
include "sseqtr4i.mm"
include "id.mm"
include "sseldi.mm"
include "sylan2.mm"
include "syl2anc.mm"
include "fsumreclf.mm"
include "adantlr.mm"
include "simplr.mm"
include "cle.mm"
include "cxr.mm"
include "0xr.mm"
include "pnfxr.mm"
include "icogelb.mm"
include "syl3anc.mm"
include "fsumlessf.mm"
include "ltletrd.mm"
include "ex.mm"
include "adantr.mm"
include "3adantl2.mm"
include "reximdva.mm"
include "mpd.mm"
include "3exp.mm"
include "rexlimdv.mm"

theorem sge0uzfsumgt
  let wph: wff ph
  let cB: class B
  let cC: class C
  let vk: setvar k
  let vm: setvar m
  let cK: class K
  let cZ: class Z
  let vx: setvar x
  assume sge0uzfsumgt.p: |- F/ k ph
  assume sge0uzfsumgt.h: |- ( ph -> K e. ZZ )
  assume sge0uzfsumgt.z: |- Z = ( ZZ>= ` K )
  assume sge0uzfsumgt.b: |- ( ( ph /\ k e. Z ) -> B e. ( 0 [,) +oo ) )
  assume sge0uzfsumgt.c: |- ( ph -> C e. RR )
  assume sge0uzfsumgt.l: |- ( ph -> C < ( sum^ ` ( k e. Z |-> B ) ) )

  disjoint B m
  disjoint C m
  disjoint K k
  disjoint K m
  disjoint k m
  disjoint Z k
  disjoint Z m
  disjoint m ph
  disjoint B x
  disjoint m x
  disjoint C x
  disjoint K x
  disjoint k x
  disjoint Z x
  disjoint ph x
  disjoint k x
  assert |- ( ph -> E. m e. Z C < sum_ k e. ( K ... m ) B )

  proof
    wph
    cC
    vx
    cv
    #
    cB
    vk
    csu
    #
    clt
    wbr
    #
    vx
    cZ
    cpw
    #
    cfn
    cin
    #
    wrex
    cC
    cK
    vm
    cv
    #
    cfz
    co
    #
    cB
    vk
    csu
    #
    clt
    wbr
    #
    vm
    cZ
    wrex
    #
    wph
    vx
    cZ
    cB
    cC
    vk
    cvv
    sge0uzfsumgt.p
    cZ
    cvv
    wcel
    wph
    cZ
    cK
    cuz
    cfv
    #
    cvv
    sge0uzfsumgt.z
    cK
    cuz
    fvex
    eqeltri
    a1i
    sge0uzfsumgt.b
    sge0uzfsumgt.c
    sge0uzfsumgt.l
    sge0gtfsumgt
    wph
    @2
    @9
    vx
    @4
    wph
    @0
    @4
    wcel
    #
    @2
    @9
    wph
    @11
    @2
    w3a
    #
    @0
    @6
    wss
    #
    vm
    cZ
    wrex
    @9
    @12
    @0
    vm
    cK
    cZ
    wph
    @11
    cK
    cz
    wcel
    @2
    sge0uzfsumgt.h
    3ad2ant1
    sge0uzfsumgt.z
    @11
    wph
    @0
    cZ
    wss
    @2
    @0
    cZ
    cfn
    elpwinss
    3ad2ant2
    @11
    wph
    @0
    cfn
    wcel
    @2
    @0
    @3
    cfn
    elinel2
    3ad2ant2
    uzfissfz
    @12
    @13
    @8
    vm
    cZ
    wph
    @2
    @5
    cZ
    wcel
    #
    @13
    @8
    wi
    #
    @11
    wph
    @2
    wa
    #
    @15
    @14
    @16
    @13
    @8
    @16
    @13
    wa
    cC
    @1
    @7
    wph
    cC
    cr
    wcel
    @2
    @13
    sge0uzfsumgt.c
    ad2antrr
    wph
    @13
    @1
    cr
    wcel
    @2
    wph
    @13
    wa
    #
    @0
    cB
    vk
    wph
    @13
    vk
    sge0uzfsumgt.p
    @13
    vk
    nfv
    nfan
    #
    @17
    @6
    @0
    @17
    cK
    @5
    fzfid
    #
    wph
    @13
    simpr
    #
    ssfid
    @17
    vk
    cv
    #
    @0
    wcel
    #
    wa
    wph
    @21
    @6
    wcel
    #
    cB
    cr
    wcel
    #
    wph
    @13
    @22
    simpll
    @17
    @0
    @6
    @21
    @20
    sselda
    wph
    @23
    wa
    #
    cc0
    cpnf
    cico
    co
    #
    cr
    cB
    rge0ssre
    @23
    wph
    @21
    cZ
    wcel
    cB
    @26
    wcel
    #
    @23
    @6
    cZ
    @21
    @6
    @10
    cZ
    cK
    @5
    fzssuz
    sge0uzfsumgt.z
    sseqtr4i
    @23
    id
    sseldi
    sge0uzfsumgt.b
    sylan2
    #
    sseldi
    #
    syl2anc
    fsumreclf
    adantlr
    wph
    @7
    cr
    wcel
    @2
    @13
    wph
    @6
    cB
    vk
    sge0uzfsumgt.p
    wph
    cK
    @5
    fzfid
    @29
    fsumreclf
    ad2antrr
    wph
    @2
    @13
    simplr
    wph
    @13
    @1
    @7
    cle
    wbr
    @2
    @17
    @6
    cB
    @0
    vk
    @18
    @19
    wph
    @23
    @24
    @13
    @29
    adantlr
    wph
    @23
    cc0
    cB
    cle
    wbr
    #
    @13
    @25
    cc0
    cxr
    wcel
    #
    cpnf
    cxr
    wcel
    #
    @27
    @30
    @31
    @25
    0xr
    a1i
    @32
    @25
    pnfxr
    a1i
    @28
    cc0
    cpnf
    cB
    icogelb
    syl3anc
    adantlr
    @20
    fsumlessf
    adantlr
    ltletrd
    ex
    adantr
    3adantl2
    reximdva
    mpd
    3exp
    rexlimdv
    mpd
end
