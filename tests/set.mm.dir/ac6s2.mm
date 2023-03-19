include "wex.mm"
include "wral.mm"
include "cvv.mm"
include "wrex.mm"
include "cv.mm"
include "wfn.mm"
include "wa.mm"
include "rexv.mm"
include "ralbii.mm"
include "wf.mm"
include "ac6s.mm"
include "ffn.mm"
include "anim1i.mm"
include "eximi.mm"
include "syl.mm"
include "sylbir.mm"

theorem ac6s2
  let wph: wff ph
  let wps: wff ps
  let vx: setvar x
  let vy: setvar y
  let cA: class A
  let vf: setvar f
  let vz: setvar z
  let cB: class B
  assume ac6s.1: |- A e. _V
  assume ac6s.2: |- ( y = ( f ` x ) -> ( ph <-> ps ) )

  disjoint f x
  disjoint A x
  disjoint A f
  disjoint x y
  disjoint f y
  disjoint f ph
  disjoint ps y
  disjoint x z
  disjoint f z
  disjoint A z
  disjoint B x
  disjoint y z
  disjoint B y
  disjoint B f
  disjoint B z
  disjoint ph z
  disjoint ps z
  assert |- ( A. x e. A E. y ph -> E. f ( f Fn A /\ A. x e. A ps ) )

  proof
    wph
    vy
    wex
    #
    vx
    cA
    wral
    wph
    vy
    cvv
    wrex
    #
    vx
    cA
    wral
    #
    vf
    cv
    #
    cA
    wfn
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
    @1
    @0
    vx
    cA
    wph
    vy
    rexv
    ralbii
    @2
    cA
    cvv
    @3
    wf
    #
    @5
    wa
    #
    vf
    wex
    @7
    wph
    wps
    vx
    vy
    cA
    cvv
    vf
    ac6s.1
    ac6s.2
    ac6s
    @9
    @6
    vf
    @8
    @4
    @5
    cA
    cvv
    @3
    ffn
    anim1i
    eximi
    syl
    sylbir
end
