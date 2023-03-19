include "wrex.mm"
include "wral.mm"
include "wsb.mm"
include "cv.mm"
include "wf.mm"
include "wa.mm"
include "wex.mm"
include "nfcv.mm"
include "nfv.mm"
include "nfs1v.mm"
include "sbequ12.mm"
include "cbvrexf.mm"
include "ralbii.mm"
include "cfv.mm"
include "sbhypf.mm"
include "ac6s.mm"
include "sylbi.mm"

theorem ac6sf2
  let wph: wff ph
  let wps: wff ps
  let vx: setvar x
  let vy: setvar y
  let cA: class A
  let cB: class B
  let vf: setvar f
  let vz: setvar z
  assume ac6sf2.y: |- F/_ y B
  assume ac6sf2.1: |- F/ y ps
  assume ac6sf2.2: |- A e. _V
  assume ac6sf2.3: |- ( y = ( f ` x ) -> ( ph <-> ps ) )

  disjoint f x
  disjoint A f
  disjoint A x
  disjoint B x
  disjoint B f
  disjoint f ph
  disjoint x y
  disjoint f y
  disjoint f z
  disjoint x z
  disjoint A z
  disjoint B z
  disjoint ph z
  disjoint ps z
  disjoint y z
  assert |- ( A. x e. A E. y e. B ph -> E. f ( f : A --> B /\ A. x e. A ps ) )

  proof
    wph
    vy
    cB
    wrex
    #
    vx
    cA
    wral
    wph
    vy
    vz
    wsb
    #
    vz
    cB
    wrex
    #
    vx
    cA
    wral
    cA
    cB
    vf
    cv
    #
    wf
    wps
    vx
    cA
    wral
    wa
    vf
    wex
    @0
    @2
    vx
    cA
    wph
    @1
    vy
    vz
    cB
    ac6sf2.y
    vz
    cB
    nfcv
    wph
    vz
    nfv
    wph
    vy
    vz
    nfs1v
    wph
    vy
    vz
    sbequ12
    cbvrexf
    ralbii
    @1
    wps
    vx
    vz
    cA
    cB
    vf
    ac6sf2.2
    wph
    wps
    vy
    vz
    vx
    cv
    @3
    cfv
    ac6sf2.1
    ac6sf2.3
    sbhypf
    ac6s
    sylbi
end
