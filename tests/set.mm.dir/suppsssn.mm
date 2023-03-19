include "csn.mm"
include "cv.mm"
include "cdif.mm"
include "wcel.mm"
include "wne.mm"
include "wa.mm"
include "wceq.mm"
include "eldifsn.mm"
include "3expb.mm"
include "sylan2b.mm"
include "suppss2.mm"

theorem suppsssn
  let wph: wff ph
  let cA: class A
  let cB: class B
  let vk: setvar k
  let cV: class V
  let cW: class W
  let cZ: class Z
  assume suppsssn.n: |- ( ( ph /\ k e. A /\ k =/= W ) -> B = Z )
  assume suppsssn.a: |- ( ph -> A e. V )

  disjoint A k
  disjoint k ph
  disjoint W k
  disjoint Z k
  assert |- ( ph -> ( ( k e. A |-> B ) supp Z ) C_ { W } )

  proof
    wph
    cA
    cB
    vk
    cV
    cW
    csn
    #
    cZ
    vk
    cv
    #
    cA
    @0
    cdif
    wcel
    wph
    @1
    cA
    wcel
    #
    @1
    cW
    wne
    #
    wa
    cB
    cZ
    wceq
    #
    @1
    cA
    cW
    eldifsn
    wph
    @2
    @3
    @4
    suppsssn.n
    3expb
    sylan2b
    suppsssn.a
    suppss2
end
