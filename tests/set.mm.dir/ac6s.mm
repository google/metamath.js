include "wrex.mm"
include "wral.mm"
include "cv.mm"
include "wss.mm"
include "wa.mm"
include "wex.mm"
include "wf.mm"
include "bnd2.mm"
include "vex.mm"
include "ac6.mm"
include "anim2i.mm"
include "eximi.mm"
include "fss.mm"
include "expcom.mm"
include "anim1d.mm"
include "eximdv.mm"
include "imp.mm"
include "exlimiv.mm"
include "3syl.mm"

theorem ac6s
  let wph: wff ph
  let wps: wff ps
  let vx: setvar x
  let vy: setvar y
  let cA: class A
  let cB: class B
  let vf: setvar f
  let vz: setvar z
  assume ac6s.1: |- A e. _V
  assume ac6s.2: |- ( y = ( f ` x ) -> ( ph <-> ps ) )

  disjoint f x
  disjoint A x
  disjoint A f
  disjoint x y
  disjoint B x
  disjoint f y
  disjoint B y
  disjoint B f
  disjoint f ph
  disjoint ps y
  disjoint x z
  disjoint f z
  disjoint A z
  disjoint y z
  disjoint B z
  disjoint ph z
  disjoint ps z
  assert |- ( A. x e. A E. y e. B ph -> E. f ( f : A --> B /\ A. x e. A ps ) )

  proof
    wph
    vy
    cB
    wrex
    vx
    cA
    wral
    vz
    cv
    #
    cB
    wss
    #
    wph
    vy
    @0
    wrex
    vx
    cA
    wral
    #
    wa
    #
    vz
    wex
    @1
    cA
    @0
    vf
    cv
    #
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
    wa
    #
    vz
    wex
    cA
    cB
    @4
    wf
    #
    @6
    wa
    #
    vf
    wex
    #
    wph
    vx
    vy
    vz
    cA
    cB
    ac6s.1
    bnd2
    @3
    @9
    vz
    @2
    @8
    @1
    wph
    wps
    vx
    vy
    cA
    @0
    vf
    ac6s.1
    vz
    vex
    ac6s.2
    ac6
    anim2i
    eximi
    @9
    @12
    vz
    @1
    @8
    @12
    @1
    @7
    @11
    vf
    @1
    @5
    @10
    @6
    @5
    @1
    @10
    cA
    @0
    cB
    @4
    fss
    expcom
    anim1d
    eximdv
    imp
    exlimiv
    3syl
end
