include "cv.mm"
include "wcel.mm"
include "wa.mm"
include "ciun.mm"
include "cin.mm"
include "c0.mm"
include "wne.mm"
include "cdif.mm"
include "wss.mm"
include "cun.mm"
include "biid.mm"
include "iunconnlem2.mm"

theorem iunconnALT
  let wph: wff ph
  let cA: class A
  let cB: class B
  let cP: class P
  let vk: setvar k
  let cJ: class J
  let cX: class X
  let vu: setvar u
  let vv: setvar v
  assume iunconnALT.1: |- ( ph -> J e. ( TopOn ` X ) )
  assume iunconnALT.2: |- ( ( ph /\ k e. A ) -> B C_ X )
  assume iunconnALT.3: |- ( ( ph /\ k e. A ) -> P e. B )
  assume iunconnALT.4: |- ( ( ph /\ k e. A ) -> ( J |`t B ) e. Conn )

  disjoint k ph
  disjoint A k
  disjoint J k
  disjoint P k
  disjoint X k
  disjoint k u
  disjoint k v
  disjoint u v
  disjoint ph u
  disjoint ph v
  disjoint A u
  disjoint A v
  disjoint B u
  disjoint B v
  disjoint J u
  disjoint J v
  disjoint X u
  disjoint X v
  assert |- ( ph -> ( J |`t U_ k e. A B ) e. Conn )

  proof
    wph
    wph
    vu
    cv
    #
    cJ
    wcel
    wa
    vv
    cv
    #
    cJ
    wcel
    wa
    @0
    vk
    cA
    cB
    ciun
    #
    cin
    c0
    wne
    wa
    @1
    @2
    cin
    c0
    wne
    wa
    @0
    @1
    cin
    cX
    @2
    cdif
    wss
    wa
    @2
    @0
    @1
    cun
    wss
    wa
    #
    vv
    vu
    cA
    cB
    cP
    vk
    cJ
    cX
    @3
    biid
    iunconnALT.1
    iunconnALT.2
    iunconnALT.3
    iunconnALT.4
    iunconnlem2
end
