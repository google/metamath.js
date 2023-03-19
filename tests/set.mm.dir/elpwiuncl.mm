include "ciun.mm"
include "cpw.mm"
include "wcel.mm"
include "wss.mm"
include "wral.mm"
include "cv.mm"
include "wa.mm"
include "elpwid.mm"
include "ralrimiva.mm"
include "iunss.mm"
include "sylibr.mm"
include "cvv.mm"
include "wb.mm"
include "jca.mm"
include "iunexg.mm"
include "elpwg.mm"
include "3syl.mm"
include "mpbird.mm"

theorem elpwiuncl
  let wph: wff ph
  let cA: class A
  let cB: class B
  let cC: class C
  let vk: setvar k
  let cV: class V
  assume elpwiuncl.1: |- ( ph -> A e. V )
  assume elpwiuncl.2: |- ( ( ph /\ k e. A ) -> B e. ~P C )

  disjoint A k
  disjoint C k
  disjoint k ph
  assert |- ( ph -> U_ k e. A B e. ~P C )

  proof
    wph
    vk
    cA
    cB
    ciun
    #
    cC
    cpw
    #
    wcel
    #
    @0
    cC
    wss
    #
    wph
    cB
    cC
    wss
    #
    vk
    cA
    wral
    @3
    wph
    @4
    vk
    cA
    wph
    vk
    cv
    cA
    wcel
    wa
    cB
    cC
    elpwiuncl.2
    elpwid
    ralrimiva
    vk
    cA
    cB
    cC
    iunss
    sylibr
    wph
    cA
    cV
    wcel
    #
    cB
    @1
    wcel
    #
    vk
    cA
    wral
    #
    wa
    @0
    cvv
    wcel
    @2
    @3
    wb
    wph
    @5
    @7
    elpwiuncl.1
    wph
    @6
    vk
    cA
    elpwiuncl.2
    ralrimiva
    jca
    vk
    cA
    cB
    cV
    @1
    iunexg
    @0
    cC
    cvv
    elpwg
    3syl
    mpbird
end
