include "c0.mm"
include "wceq.mm"
include "wb.mm"
include "wa.mm"
include "wn.mm"
include "wo.mm"
include "wral.mm"
include "dfbi3.mm"
include "rzal.mm"
include "adantr.mm"
include "adantl.mm"
include "pm5.1.mm"
include "syl12anc.mm"
include "wne.mm"
include "df-ne.mm"
include "r19.28z.mm"
include "ralbidv.mm"
include "sylbir.mm"
include "nfcv.mm"
include "nfral.mm"
include "r19.27z.mm"
include "sylan9bbr.mm"
include "jaoi.mm"
include "sylbi.mm"

theorem raaan2
  let wph: wff ph
  let wps: wff ps
  let vx: setvar x
  let vy: setvar y
  let cA: class A
  let cB: class B
  let vk: setvar k
  assume raaan2.1: |- F/ y ph
  assume raaan2.2: |- F/ x ps

  disjoint x y
  disjoint A x
  disjoint A y
  disjoint B x
  disjoint B y
  disjoint k x
  assert |- ( ( A = (/) <-> B = (/) ) -> ( A. x e. A A. y e. B ( ph /\ ps ) <-> ( A. x e. A ph /\ A. y e. B ps ) ) )

  proof
    cA
    c0
    wceq
    #
    cB
    c0
    wceq
    #
    wb
    @0
    @1
    wa
    #
    @0
    wn
    #
    @1
    wn
    #
    wa
    #
    wo
    wph
    wps
    wa
    vy
    cB
    wral
    #
    vx
    cA
    wral
    #
    wph
    vx
    cA
    wral
    #
    wps
    vy
    cB
    wral
    #
    wa
    #
    wb
    #
    @0
    @1
    dfbi3
    @2
    @11
    @5
    @2
    @7
    @8
    @9
    @11
    @0
    @7
    @1
    @6
    vx
    cA
    rzal
    adantr
    @0
    @8
    @1
    wph
    vx
    cA
    rzal
    adantr
    @1
    @9
    @0
    wps
    vy
    cB
    rzal
    adantl
    @7
    @10
    pm5.1
    syl12anc
    @4
    @7
    wph
    @9
    wa
    #
    vx
    cA
    wral
    #
    @3
    @10
    @4
    cB
    c0
    wne
    #
    @7
    @13
    wb
    cB
    c0
    df-ne
    @14
    @6
    @12
    vx
    cA
    wph
    wps
    vy
    cB
    raaan2.1
    r19.28z
    ralbidv
    sylbir
    @3
    cA
    c0
    wne
    @13
    @10
    wb
    cA
    c0
    df-ne
    wph
    @9
    vx
    cA
    wps
    vx
    vy
    cB
    vx
    cB
    nfcv
    raaan2.2
    nfral
    r19.27z
    sylbir
    sylan9bbr
    jaoi
    sylbi
end
