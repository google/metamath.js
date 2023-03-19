include "com.mm"
include "csdm.mm"
include "wbr.mm"
include "cv.mm"
include "cfv.mm"
include "wcel.mm"
include "wral.mm"
include "wex.mm"
include "wa.mm"
include "wfn.mm"
include "cfn.mm"
include "isfinite2.mm"
include "adantl.mm"
include "simpr.mm"
include "c0.mm"
include "wne.mm"
include "adantlr.mm"
include "choicefi.mm"
include "wi.mm"
include "a1i.mm"
include "eximdv.mm"
include "mpd.mm"
include "wn.mm"
include "cen.mm"
include "cdom.mm"
include "anim1i.mm"
include "bren2.mm"
include "sylibr.mm"
include "axccd.mm"
include "syldan.mm"
include "pm2.61dan.mm"

theorem axccd2
  let wph: wff ph
  let vx: setvar x
  let cA: class A
  let vf: setvar f
  assume axccd2.1: |- ( ph -> A ~<_ _om )
  assume axccd2.2: |- ( ( ph /\ x e. A ) -> x =/= (/) )

  disjoint A f
  disjoint A x
  disjoint f x
  disjoint f ph
  disjoint ph x
  assert |- ( ph -> E. f A. x e. A ( f ` x ) e. x )

  proof
    wph
    cA
    com
    csdm
    wbr
    #
    vx
    cv
    #
    vf
    cv
    #
    cfv
    @1
    wcel
    vx
    cA
    wral
    #
    vf
    wex
    #
    wph
    @0
    wa
    #
    @2
    cA
    wfn
    #
    @3
    wa
    #
    vf
    wex
    @4
    @5
    vx
    cA
    @1
    vf
    cA
    @0
    cA
    cfn
    wcel
    wph
    cA
    isfinite2
    adantl
    @5
    @1
    cA
    wcel
    #
    simpr
    wph
    @8
    @1
    c0
    wne
    #
    @0
    axccd2.2
    adantlr
    choicefi
    @5
    @7
    @3
    vf
    @7
    @3
    wi
    @5
    @6
    @3
    simpr
    a1i
    eximdv
    mpd
    wph
    @0
    wn
    #
    cA
    com
    cen
    wbr
    #
    @4
    wph
    @10
    wa
    cA
    com
    cdom
    wbr
    #
    @10
    wa
    @11
    wph
    @12
    @10
    axccd2.1
    anim1i
    cA
    com
    bren2
    sylibr
    wph
    @11
    wa
    vx
    cA
    vf
    wph
    @11
    simpr
    wph
    @8
    @9
    @11
    axccd2.2
    adantlr
    axccd
    syldan
    pm2.61dan
end
