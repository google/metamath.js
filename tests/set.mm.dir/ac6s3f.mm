include "wex.mm"
include "wral.mm"
include "cvv.mm"
include "wrex.mm"
include "cv.mm"
include "wf.mm"
include "wa.mm"
include "rexv.mm"
include "ralbii.mm"
include "biimpri.mm"
include "ac6sf.mm"
include "exsimpr.mm"
include "3syl.mm"

theorem ac6s3f
  let wph: wff ph
  let wps: wff ps
  let vx: setvar x
  let vy: setvar y
  let cA: class A
  let vf: setvar f
  assume ac6s3f.1: |- F/ y ps
  assume ac6s3f.2: |- A e. _V
  assume ac6s3f.3: |- ( y = ( f ` x ) -> ( ph <-> ps ) )

  disjoint f ph
  disjoint x y
  disjoint A x
  disjoint f x
  disjoint f y
  disjoint A f
  assert |- ( A. x e. A E. y ph -> E. f A. x e. A ps )

  proof
    wph
    vy
    wex
    #
    vx
    cA
    wral
    #
    wph
    vy
    cvv
    wrex
    #
    vx
    cA
    wral
    #
    cA
    cvv
    vf
    cv
    wf
    #
    wps
    vx
    cA
    wral
    #
    wa
    vf
    wex
    @5
    vf
    wex
    @3
    @1
    @2
    @0
    vx
    cA
    wph
    vy
    rexv
    ralbii
    biimpri
    wph
    wps
    vx
    vy
    cA
    cvv
    vf
    ac6s3f.1
    ac6s3f.2
    ac6s3f.3
    ac6sf
    @4
    @5
    vf
    exsimpr
    3syl
end
