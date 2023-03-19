include "c0.mm"
include "wne.mm"
include "wral.mm"
include "wa.mm"
include "r19.3rz.mm"
include "anbi2d.mm"
include "r19.26.mm"
include "syl6rbbr.mm"

theorem r19.27z
  let wph: wff ph
  let wps: wff ps
  let vx: setvar x
  let cA: class A
  assume r19.27z.1: |- F/ x ps

  disjoint A x
  assert |- ( A =/= (/) -> ( A. x e. A ( ph /\ ps ) <-> ( A. x e. A ph /\ ps ) ) )

  proof
    cA
    c0
    wne
    #
    wph
    vx
    cA
    wral
    #
    wps
    wa
    @1
    wps
    vx
    cA
    wral
    #
    wa
    wph
    wps
    wa
    vx
    cA
    wral
    @0
    wps
    @2
    @1
    wps
    vx
    cA
    r19.27z.1
    r19.3rz
    anbi2d
    wph
    wps
    vx
    cA
    r19.26
    syl6rbbr
end
