include "c0.mm"
include "wne.mm"
include "wral.mm"
include "wa.mm"
include "r19.3rz.mm"
include "anbi1d.mm"
include "r19.26.mm"
include "syl6rbbr.mm"

theorem r19.28z
  let wph: wff ph
  let wps: wff ps
  let vx: setvar x
  let cA: class A
  assume r19.3rz.1: |- F/ x ph

  disjoint A x
  assert |- ( A =/= (/) -> ( A. x e. A ( ph /\ ps ) <-> ( ph /\ A. x e. A ps ) ) )

  proof
    cA
    c0
    wne
    #
    wph
    wps
    vx
    cA
    wral
    #
    wa
    wph
    vx
    cA
    wral
    #
    @1
    wa
    wph
    wps
    wa
    vx
    cA
    wral
    @0
    wph
    @2
    @1
    wph
    vx
    cA
    r19.3rz.1
    r19.3rz
    anbi1d
    wph
    wps
    vx
    cA
    r19.26
    syl6rbbr
end
