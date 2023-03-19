include "caddc.mm"
include "cseq.mm"
include "cuz.mm"
include "cfv.mm"
include "wcel.mm"
include "cz.mm"
include "syl6eleq.mm"
include "eluzel2.mm"
include "syl.mm"
include "cr.mm"
include "cv.mm"
include "serfre.mm"
include "ffvelrnda.mm"
include "wa.mm"
include "simpr.mm"
include "cfz.mm"
include "co.mm"
include "simpl.mm"
include "elfzuz.mm"
include "syl6eleqr.mm"
include "syl2an.mm"
include "cle.mm"
include "wbr.mm"
include "serle.mm"
include "climle.mm"

theorem cvgcmpub
  let wph: wff ph
  let cA: class A
  let cB: class B
  let vk: setvar k
  let cF: class F
  let cG: class G
  let cM: class M
  let cN: class N
  let cZ: class Z
  let vn: setvar n
  let vm: setvar m
  let vx: setvar x
  assume cvgcmp.1: |- Z = ( ZZ>= ` M )
  assume cvgcmp.2: |- ( ph -> N e. Z )
  assume cvgcmp.3: |- ( ( ph /\ k e. Z ) -> ( F ` k ) e. RR )
  assume cvgcmp.4: |- ( ( ph /\ k e. Z ) -> ( G ` k ) e. RR )
  assume cvgcmpub.5: |- ( ph -> seq M ( + , F ) ~~> A )
  assume cvgcmpub.6: |- ( ph -> seq M ( + , G ) ~~> B )
  assume cvgcmpub.7: |- ( ( ph /\ k e. Z ) -> ( G ` k ) <_ ( F ` k ) )

  disjoint F k
  disjoint G k
  disjoint k ph
  disjoint M k
  disjoint N k
  disjoint Z k
  disjoint A n
  disjoint B n
  disjoint k m
  disjoint k n
  disjoint k x
  disjoint m n
  disjoint m x
  disjoint F m
  disjoint n x
  disjoint F n
  disjoint F x
  disjoint G m
  disjoint G n
  disjoint G x
  disjoint m ph
  disjoint n ph
  disjoint ph x
  disjoint M m
  disjoint M n
  disjoint M x
  disjoint N m
  disjoint N n
  disjoint N x
  disjoint Z m
  disjoint Z n
  disjoint Z x
  assert |- ( ph -> B <_ A )

  proof
    wph
    cB
    cA
    vn
    caddc
    cG
    cM
    cseq
    #
    caddc
    cF
    cM
    cseq
    #
    cM
    cZ
    cvgcmp.1
    wph
    cN
    cM
    cuz
    cfv
    #
    wcel
    cM
    cz
    wcel
    wph
    cN
    cZ
    @2
    cvgcmp.2
    cvgcmp.1
    syl6eleq
    cM
    cN
    eluzel2
    syl
    #
    cvgcmpub.6
    cvgcmpub.5
    wph
    cZ
    cr
    vn
    cv
    #
    @0
    wph
    vk
    cG
    cM
    cZ
    cvgcmp.1
    @3
    cvgcmp.4
    serfre
    ffvelrnda
    wph
    cZ
    cr
    @4
    @1
    wph
    vk
    cF
    cM
    cZ
    cvgcmp.1
    @3
    cvgcmp.3
    serfre
    ffvelrnda
    wph
    @4
    cZ
    wcel
    #
    wa
    #
    vk
    cG
    cF
    cM
    @4
    @6
    @4
    cZ
    @2
    wph
    @5
    simpr
    cvgcmp.1
    syl6eleq
    @6
    wph
    vk
    cv
    #
    cZ
    wcel
    #
    @7
    cG
    cfv
    #
    cr
    wcel
    @7
    cM
    @4
    cfz
    co
    wcel
    #
    wph
    @5
    simpl
    #
    @10
    @7
    @2
    cZ
    @7
    cM
    @4
    elfzuz
    cvgcmp.1
    syl6eleqr
    #
    cvgcmp.4
    syl2an
    @6
    wph
    @8
    @7
    cF
    cfv
    #
    cr
    wcel
    @10
    @11
    @12
    cvgcmp.3
    syl2an
    @6
    wph
    @8
    @9
    @13
    cle
    wbr
    @10
    @11
    @12
    cvgcmpub.7
    syl2an
    serle
    climle
end
