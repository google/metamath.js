include "cv.mm"
include "cfv.mm"
include "cabs.mm"
include "cle.mm"
include "wbr.mm"
include "wral.mm"
include "cr.mm"
include "wrex.mm"
include "cz.mm"
include "wcel.mm"
include "cli.mm"
include "cdm.mm"
include "cc.mm"
include "wa.mm"
include "ffvelrnda.mm"
include "recnd.mm"
include "ralrimia.mm"
include "climbddf.mm"
include "syl3anc.mm"
include "cneg.mm"
include "renegcl.mm"
include "ad2antlr.mm"
include "nfv.mm"
include "nfan.mm"
include "nfra1.mm"
include "simpll.mm"
include "simpr.mm"
include "rspa.mm"
include "adantll.mm"
include "ad4ant13.mm"
include "simpllr.mm"
include "absled.mm"
include "mpbid.mm"
include "simpld.mm"
include "syl21anc.mm"
include "ex.mm"
include "ralrimi.mm"
include "wceq.mm"
include "breq1.mm"
include "ralbidv.mm"
include "rspcev.mm"
include "syl2anc.mm"
include "rexlimdva.mm"
include "mpd.mm"
include "climinf2.mm"

theorem climinf3
  let wph: wff ph
  let vk: setvar k
  let cF: class F
  let cM: class M
  let cZ: class Z
  let vx: setvar x
  let vy: setvar y
  assume climinf3.1: |- F/ k ph
  assume climinf3.2: |- F/_ k F
  assume climinf3.3: |- ( ph -> M e. ZZ )
  assume climinf3.4: |- Z = ( ZZ>= ` M )
  assume climinf3.5: |- ( ph -> F : Z --> RR )
  assume climinf3.6: |- ( ( ph /\ k e. Z ) -> ( F ` ( k + 1 ) ) <_ ( F ` k ) )
  assume climinf3.7: |- ( ph -> F e. dom ~~> )

  disjoint M k
  disjoint Z k
  disjoint F x
  disjoint F y
  disjoint x y
  disjoint M x
  disjoint k x
  disjoint Z x
  disjoint Z y
  disjoint k y
  disjoint ph x
  assert |- ( ph -> F ~~> inf ( ran F , RR* , < ) )

  proof
    wph
    vy
    vk
    cF
    cM
    cZ
    climinf3.1
    climinf3.2
    climinf3.4
    climinf3.3
    climinf3.5
    climinf3.6
    wph
    vk
    cv
    #
    cF
    cfv
    #
    cabs
    cfv
    vx
    cv
    #
    cle
    wbr
    #
    vk
    cZ
    wral
    #
    vx
    cr
    wrex
    #
    vy
    cv
    #
    @1
    cle
    wbr
    #
    vk
    cZ
    wral
    #
    vy
    cr
    wrex
    #
    wph
    cM
    cz
    wcel
    cF
    cli
    cdm
    wcel
    @1
    cc
    wcel
    #
    vk
    cZ
    wral
    @5
    climinf3.3
    climinf3.7
    wph
    @10
    vk
    cZ
    climinf3.1
    wph
    @0
    cZ
    wcel
    #
    wa
    @1
    wph
    cZ
    cr
    @0
    cF
    climinf3.5
    ffvelrnda
    #
    recnd
    ralrimia
    vx
    vk
    cF
    cM
    cZ
    climinf3.2
    climinf3.4
    climbddf
    syl3anc
    wph
    @4
    @9
    vx
    cr
    wph
    @2
    cr
    wcel
    #
    wa
    #
    @4
    @9
    @14
    @4
    wa
    #
    @2
    cneg
    #
    cr
    wcel
    #
    @16
    @1
    cle
    wbr
    #
    vk
    cZ
    wral
    #
    @9
    @13
    @17
    wph
    @4
    @2
    renegcl
    ad2antlr
    @15
    @18
    vk
    cZ
    @14
    @4
    vk
    wph
    @13
    vk
    climinf3.1
    @13
    vk
    nfv
    nfan
    @3
    vk
    cZ
    nfra1
    nfan
    @15
    @11
    @18
    @15
    @11
    wa
    @14
    @11
    @3
    @18
    @14
    @4
    @11
    simpll
    @15
    @11
    simpr
    @4
    @11
    @3
    @14
    @3
    vk
    cZ
    rspa
    adantll
    @14
    @11
    wa
    #
    @3
    wa
    #
    @18
    @1
    @2
    cle
    wbr
    #
    @21
    @3
    @18
    @22
    wa
    @20
    @3
    simpr
    @21
    @1
    @2
    wph
    @11
    @1
    cr
    wcel
    @13
    @3
    @12
    ad4ant13
    wph
    @13
    @11
    @3
    simpllr
    absled
    mpbid
    simpld
    syl21anc
    ex
    ralrimi
    @8
    @19
    vy
    @16
    cr
    @6
    @16
    wceq
    @7
    @18
    vk
    cZ
    @6
    @16
    @1
    cle
    breq1
    ralbidv
    rspcev
    syl2anc
    ex
    rexlimdva
    mpd
    climinf2
end
