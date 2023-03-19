include "cc0.mm"
include "csu.mm"
include "cmin.mm"
include "co.mm"
include "cle.mm"
include "wbr.mm"
include "cv.mm"
include "wcel.mm"
include "wa.mm"
include "resubcld.mm"
include "subge0d.mm"
include "mpbird.mm"
include "fsumge0.mm"
include "recnd.mm"
include "fsumsub.mm"
include "breqtrd.mm"
include "fsumrecl.mm"
include "mpbid.mm"

theorem fsumle
  let wph: wff ph
  let cA: class A
  let cB: class B
  let cC: class C
  let vk: setvar k
  assume fsumle.1: |- ( ph -> A e. Fin )
  assume fsumle.2: |- ( ( ph /\ k e. A ) -> B e. RR )
  assume fsumle.3: |- ( ( ph /\ k e. A ) -> C e. RR )
  assume fsumle.4: |- ( ( ph /\ k e. A ) -> B <_ C )

  disjoint A k
  disjoint k ph
  assert |- ( ph -> sum_ k e. A B <_ sum_ k e. A C )

  proof
    wph
    cc0
    cA
    cC
    vk
    csu
    #
    cA
    cB
    vk
    csu
    #
    cmin
    co
    #
    cle
    wbr
    @1
    @0
    cle
    wbr
    wph
    cc0
    cA
    cC
    cB
    cmin
    co
    #
    vk
    csu
    @2
    cle
    wph
    cA
    @3
    vk
    fsumle.1
    wph
    vk
    cv
    cA
    wcel
    wa
    #
    cC
    cB
    fsumle.3
    fsumle.2
    resubcld
    @4
    cc0
    @3
    cle
    wbr
    cB
    cC
    cle
    wbr
    fsumle.4
    @4
    cC
    cB
    fsumle.3
    fsumle.2
    subge0d
    mpbird
    fsumge0
    wph
    cA
    cC
    cB
    vk
    fsumle.1
    @4
    cC
    fsumle.3
    recnd
    @4
    cB
    fsumle.2
    recnd
    fsumsub
    breqtrd
    wph
    @0
    @1
    wph
    cA
    cC
    vk
    fsumle.1
    fsumle.3
    fsumrecl
    wph
    cA
    cB
    vk
    fsumle.1
    fsumle.2
    fsumrecl
    subge0d
    mpbid
end
