include "wa.mm"
include "wral.mm"
include "wb.mm"
include "c0.mm"
include "wceq.mm"
include "rzal.mm"
include "pm5.1.mm"
include "syl12anc.mm"
include "wne.mm"
include "r19.28z.mm"
include "ralbidv.mm"
include "nfcv.mm"
include "nfral.mm"
include "r19.27z.mm"
include "bitrd.mm"
include "pm2.61ine.mm"

theorem raaan
  let wph: wff ph
  let wps: wff ps
  let vx: setvar x
  let vy: setvar y
  let cA: class A
  assume raaan.1: |- F/ y ph
  assume raaan.2: |- F/ x ps

  disjoint x y
  disjoint A x
  disjoint A y
  assert |- ( A. x e. A A. y e. A ( ph /\ ps ) <-> ( A. x e. A ph /\ A. y e. A ps ) )

  proof
    wph
    wps
    wa
    vy
    cA
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
    cA
    wral
    #
    wa
    #
    wb
    #
    cA
    c0
    cA
    c0
    wceq
    @1
    @2
    @3
    @5
    @0
    vx
    cA
    rzal
    wph
    vx
    cA
    rzal
    wps
    vy
    cA
    rzal
    @1
    @4
    pm5.1
    syl12anc
    cA
    c0
    wne
    #
    @1
    wph
    @3
    wa
    #
    vx
    cA
    wral
    @4
    @6
    @0
    @7
    vx
    cA
    wph
    wps
    vy
    cA
    raaan.1
    r19.28z
    ralbidv
    wph
    @3
    vx
    cA
    wps
    vx
    vy
    cA
    vx
    cA
    nfcv
    raaan.2
    nfral
    r19.27z
    bitrd
    pm2.61ine
end
