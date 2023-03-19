include "csu.mm"
include "cli.mm"
include "wbr.mm"
include "cv.mm"
include "cfv.mm"
include "cmpt.mm"
include "mpteq2dva.mm"
include "crli.mm"
include "cvv.mm"
include "cr.mm"
include "wss.mm"
include "cz.mm"
include "cuz.mm"
include "uzssz.mm"
include "eqsstri.mm"
include "zssre.mm"
include "sstri.mm"
include "a1i.mm"
include "wcel.mm"
include "wa.mm"
include "fvexd.mm"
include "wb.mm"
include "adantr.mm"
include "climrel.mm"
include "brrelexi.mm"
include "syl.mm"
include "eqid.mm"
include "climmpt.mm"
include "syl2anc.mm"
include "mpbid.mm"
include "cc.mm"
include "anassrs.mm"
include "fmptd.mm"
include "rlimclim.mm"
include "mpbird.mm"
include "fsumrlim.mm"
include "cfn.mm"
include "anass1rs.mm"
include "fsumcl.mm"
include "eqbrtrd.mm"

theorem climfsum
  let wph: wff ph
  let cA: class A
  let cB: class B
  let vk: setvar k
  let vn: setvar n
  let cF: class F
  let cH: class H
  let cM: class M
  let cW: class W
  let cZ: class Z
  assume climfsum.1: |- Z = ( ZZ>= ` M )
  assume climfsum.2: |- ( ph -> M e. ZZ )
  assume climfsum.3: |- ( ph -> A e. Fin )
  assume climfsum.5: |- ( ( ph /\ k e. A ) -> F ~~> B )
  assume climfsum.6: |- ( ph -> H e. W )
  assume climfsum.7: |- ( ( ph /\ ( k e. A /\ n e. Z ) ) -> ( F ` n ) e. CC )
  assume climfsum.8: |- ( ( ph /\ n e. Z ) -> ( H ` n ) = sum_ k e. A ( F ` n ) )

  disjoint k n
  disjoint A k
  disjoint A n
  disjoint H n
  disjoint k ph
  disjoint n ph
  disjoint Z k
  disjoint Z n
  disjoint B n
  disjoint F n
  disjoint M n
  assert |- ( ph -> H ~~> sum_ k e. A B )

  proof
    wph
    cH
    cA
    cB
    vk
    csu
    #
    cli
    wbr
    #
    vn
    cZ
    vn
    cv
    #
    cH
    cfv
    #
    cmpt
    #
    @0
    cli
    wbr
    #
    wph
    @4
    vn
    cZ
    cA
    @2
    cF
    cfv
    #
    vk
    csu
    #
    cmpt
    #
    @0
    cli
    wph
    vn
    cZ
    @3
    @7
    climfsum.8
    mpteq2dva
    wph
    @8
    @0
    crli
    wbr
    @8
    @0
    cli
    wbr
    wph
    vn
    cZ
    cA
    @6
    cB
    vk
    cvv
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
    cz
    climfsum.1
    cM
    uzssz
    eqsstri
    zssre
    sstri
    a1i
    climfsum.3
    wph
    @2
    cZ
    wcel
    #
    vk
    cv
    cA
    wcel
    #
    wa
    wa
    @2
    cF
    fvexd
    wph
    @10
    wa
    #
    vn
    cZ
    @6
    cmpt
    #
    cB
    crli
    wbr
    @12
    cB
    cli
    wbr
    #
    @11
    cF
    cB
    cli
    wbr
    #
    @13
    climfsum.5
    @11
    cM
    cz
    wcel
    #
    cF
    cvv
    wcel
    #
    @14
    @13
    wb
    wph
    @15
    @10
    climfsum.2
    adantr
    #
    @11
    @14
    @16
    climfsum.5
    cF
    cB
    cli
    climrel
    brrelexi
    syl
    cB
    vn
    cF
    @12
    cM
    cvv
    cZ
    climfsum.1
    @12
    eqid
    #
    climmpt
    syl2anc
    mpbid
    @11
    cB
    @12
    cM
    cZ
    climfsum.1
    @17
    @11
    vn
    cZ
    @6
    cc
    @12
    wph
    @10
    @9
    @6
    cc
    wcel
    #
    climfsum.7
    anassrs
    @18
    fmptd
    rlimclim
    mpbird
    fsumrlim
    wph
    @0
    @8
    cM
    cZ
    climfsum.1
    climfsum.2
    wph
    vn
    cZ
    @7
    cc
    @8
    wph
    @9
    wa
    cA
    @6
    vk
    wph
    cA
    cfn
    wcel
    @9
    climfsum.3
    adantr
    wph
    @10
    @9
    @19
    climfsum.7
    anass1rs
    fsumcl
    @8
    eqid
    fmptd
    rlimclim
    mpbid
    eqbrtrd
    wph
    @15
    cH
    cW
    wcel
    @1
    @5
    wb
    climfsum.2
    climfsum.6
    @0
    vn
    cH
    @4
    cM
    cW
    cZ
    climfsum.1
    @4
    eqid
    climmpt
    syl2anc
    mpbird
end
