include "wrex.mm"
include "cv.mm"
include "wral.mm"
include "wf.mm"
include "wa.mm"
include "wex.mm"
include "wi.mm"
include "wceq.mm"
include "raleq.mm"
include "feq2.mm"
include "anbi12d.mm"
include "exbidv.mm"
include "imbi12d.mm"
include "vex.mm"
include "ac6s.mm"
include "vtoclg.mm"

theorem ac6sg
  let wph: wff ph
  let wps: wff ps
  let vx: setvar x
  let vy: setvar y
  let cA: class A
  let cB: class B
  let vf: setvar f
  let cV: class V
  let vz: setvar z
  assume ac6sg.1: |- ( y = ( f ` x ) -> ( ph <-> ps ) )

  disjoint A f
  disjoint A x
  disjoint f x
  disjoint B f
  disjoint B x
  disjoint B y
  disjoint f y
  disjoint x y
  disjoint f ph
  disjoint ps y
  disjoint A z
  disjoint f z
  disjoint x z
  disjoint B z
  disjoint y z
  disjoint ph z
  disjoint ps z
  assert |- ( A e. V -> ( A. x e. A E. y e. B ph -> E. f ( f : A --> B /\ A. x e. A ps ) ) )

  proof
    wph
    vy
    cB
    wrex
    #
    vx
    vz
    cv
    #
    wral
    #
    @1
    cB
    vf
    cv
    #
    wf
    #
    wps
    vx
    @1
    wral
    #
    wa
    #
    vf
    wex
    #
    wi
    @0
    vx
    cA
    wral
    #
    cA
    cB
    @3
    wf
    #
    wps
    vx
    cA
    wral
    #
    wa
    #
    vf
    wex
    #
    wi
    vz
    cA
    cV
    @1
    cA
    wceq
    #
    @2
    @8
    @7
    @12
    @0
    vx
    @1
    cA
    raleq
    @13
    @6
    @11
    vf
    @13
    @4
    @9
    @5
    @10
    @1
    cA
    cB
    @3
    feq2
    wps
    vx
    @1
    cA
    raleq
    anbi12d
    exbidv
    imbi12d
    wph
    wps
    vx
    vy
    @1
    cB
    vf
    vz
    vex
    ac6sg.1
    ac6s
    vtoclg
end
