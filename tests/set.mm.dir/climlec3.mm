include "cle.mm"
include "wbr.mm"
include "cneg.mm"
include "cv.mm"
include "cfv.mm"
include "cmpt.mm"
include "renegcld.mm"
include "cc0.mm"
include "cmin.mm"
include "co.mm"
include "cli.mm"
include "cvv.mm"
include "0cnd.mm"
include "wcel.mm"
include "cuz.mm"
include "fvex.mm"
include "eqeltri.mm"
include "mptex.mm"
include "a1i.mm"
include "wa.mm"
include "recnd.mm"
include "cr.mm"
include "wceq.mm"
include "simpr.mm"
include "weq.mm"
include "fveq2.mm"
include "negeqd.mm"
include "eqid.mm"
include "fvmptg.mm"
include "syl2anc.mm"
include "df-neg.mm"
include "syl6eq.mm"
include "climsubc2.mm"
include "syl6breqr.mm"
include "eqeltrd.mm"
include "adantr.mm"
include "lenegd.mm"
include "mpbid.mm"
include "breqtrrd.mm"
include "climlec2.mm"
include "climrecl.mm"
include "mpbird.mm"

theorem climlec3
  let wph: wff ph
  let cA: class A
  let cB: class B
  let vk: setvar k
  let cF: class F
  let cM: class M
  let cZ: class Z
  let vm: setvar m
  assume climlec3.1: |- Z = ( ZZ>= ` M )
  assume climlec3.2: |- ( ph -> M e. ZZ )
  assume climlec3.3: |- ( ph -> B e. RR )
  assume climlec3.4: |- ( ph -> F ~~> A )
  assume climlec3.5: |- ( ( ph /\ k e. Z ) -> ( F ` k ) e. RR )
  assume climlec3.6: |- ( ( ph /\ k e. Z ) -> ( F ` k ) <_ B )

  disjoint A k
  disjoint B k
  disjoint F k
  disjoint k ph
  disjoint M k
  disjoint Z k
  disjoint F m
  disjoint k m
  disjoint Z m
  assert |- ( ph -> A <_ B )

  proof
    wph
    cA
    cB
    cle
    wbr
    cB
    cneg
    #
    cA
    cneg
    #
    cle
    wbr
    wph
    @0
    @1
    vk
    vm
    cZ
    vm
    cv
    #
    cF
    cfv
    #
    cneg
    #
    cmpt
    #
    cM
    cZ
    climlec3.1
    climlec3.2
    wph
    cB
    climlec3.3
    renegcld
    wph
    @5
    cc0
    cA
    cmin
    co
    @1
    cli
    wph
    cA
    cc0
    vk
    cF
    @5
    cM
    cvv
    cZ
    climlec3.1
    climlec3.2
    climlec3.4
    wph
    0cnd
    @5
    cvv
    wcel
    wph
    vm
    cZ
    @4
    cZ
    cM
    cuz
    cfv
    cvv
    climlec3.1
    cM
    cuz
    fvex
    eqeltri
    mptex
    a1i
    wph
    vk
    cv
    #
    cZ
    wcel
    #
    wa
    #
    @6
    cF
    cfv
    #
    climlec3.5
    recnd
    @8
    @6
    @5
    cfv
    #
    @9
    cneg
    #
    cc0
    @9
    cmin
    co
    @8
    @7
    @11
    cr
    wcel
    @10
    @11
    wceq
    wph
    @7
    simpr
    @8
    @9
    climlec3.5
    renegcld
    #
    vm
    @6
    @4
    @11
    cZ
    cr
    @5
    vm
    vk
    weq
    @3
    @9
    @2
    @6
    cF
    fveq2
    negeqd
    @5
    eqid
    fvmptg
    syl2anc
    #
    @9
    df-neg
    syl6eq
    climsubc2
    cA
    df-neg
    syl6breqr
    @8
    @10
    @11
    cr
    @13
    @12
    eqeltrd
    @8
    @0
    @11
    @10
    cle
    @8
    @9
    cB
    cle
    wbr
    @0
    @11
    cle
    wbr
    climlec3.6
    @8
    @9
    cB
    climlec3.5
    wph
    cB
    cr
    wcel
    @7
    climlec3.3
    adantr
    lenegd
    mpbid
    @13
    breqtrrd
    climlec2
    wph
    cA
    cB
    wph
    cA
    vk
    cF
    cM
    cZ
    climlec3.1
    climlec3.2
    climlec3.4
    climlec3.5
    climrecl
    climlec3.3
    lenegd
    mpbird
end
