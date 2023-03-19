include "weq.mm"
include "cin.mm"
include "c0.mm"
include "wceq.mm"
include "wo.mm"
include "wral.mm"
include "wdisj.mm"
include "cv.mm"
include "wcel.mm"
include "wa.mm"
include "wi.mm"
include "orc.mm"
include "a1d.mm"
include "wn.mm"
include "3expia.mm"
include "con3d.mm"
include "impancom.mm"
include "ralrimiv.mm"
include "disj.mm"
include "sylibr.mm"
include "olcd.mm"
include "expcom.mm"
include "pm2.61i.mm"
include "adantr.mm"
include "ralrimivva.mm"
include "disjor.mm"

theorem disjord
  let wph: wff ph
  let vx: setvar x
  let cA: class A
  let cB: class B
  let cV: class V
  let va: setvar a
  let vb: setvar b
  assume disjord.1: |- ( a = b -> A = B )
  assume disjord.2: |- ( ( ph /\ x e. A /\ x e. B ) -> a = b )

  disjoint A b
  disjoint A x
  disjoint b x
  disjoint B a
  disjoint B x
  disjoint a x
  disjoint V a
  disjoint V b
  disjoint V x
  disjoint a b
  disjoint a ph
  disjoint b ph
  disjoint ph x
  assert |- ( ph -> Disj_ a e. V A )

  proof
    wph
    va
    vb
    weq
    #
    cA
    cB
    cin
    c0
    wceq
    #
    wo
    #
    vb
    cV
    wral
    va
    cV
    wral
    va
    cV
    cA
    wdisj
    wph
    @2
    va
    vb
    cV
    cV
    wph
    @2
    va
    cv
    cV
    wcel
    vb
    cv
    cV
    wcel
    wa
    @0
    wph
    @2
    wi
    @0
    @2
    wph
    @0
    @1
    orc
    a1d
    wph
    @0
    wn
    #
    @2
    wph
    @3
    wa
    #
    @1
    @0
    @4
    vx
    cv
    #
    cB
    wcel
    #
    wn
    #
    vx
    cA
    wral
    @1
    @4
    @7
    vx
    cA
    wph
    @5
    cA
    wcel
    #
    @3
    @7
    wph
    @8
    wa
    @6
    @0
    wph
    @8
    @6
    @0
    disjord.2
    3expia
    con3d
    impancom
    ralrimiv
    vx
    cA
    cB
    disj
    sylibr
    olcd
    expcom
    pm2.61i
    adantr
    ralrimivva
    cV
    cA
    cB
    va
    vb
    disjord.1
    disjor
    sylibr
end
