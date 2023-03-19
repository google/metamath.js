include "cv.mm"
include "c0.mm"
include "wne.mm"
include "cfv.mm"
include "wcel.mm"
include "wi.mm"
include "wral.mm"
include "wex.mm"
include "com.mm"
include "cen.mm"
include "wbr.mm"
include "cvv.mm"
include "encv.mm"
include "simpld.mm"
include "syl.mm"
include "wceq.mm"
include "breq1.mm"
include "raleq.mm"
include "exbidv.mm"
include "imbi12d.mm"
include "ax-cc.mm"
include "vtoclg.mm"
include "mpd.mm"
include "wa.mm"
include "nfv.mm"
include "nfra1.mm"
include "nfan.mm"
include "adantlr.mm"
include "rspa.mm"
include "adantll.mm"
include "ex.mm"
include "ralrimi.mm"
include "eximdv.mm"

theorem axccd
  let wph: wff ph
  let vx: setvar x
  let cA: class A
  let vf: setvar f
  let vy: setvar y
  assume axccd.1: |- ( ph -> A ~~ _om )
  assume axccd.2: |- ( ( ph /\ x e. A ) -> x =/= (/) )

  disjoint A f
  disjoint A x
  disjoint f x
  disjoint f ph
  disjoint ph x
  disjoint A y
  disjoint f y
  disjoint x y
  assert |- ( ph -> E. f A. x e. A ( f ` x ) e. x )

  proof
    wph
    vx
    cv
    #
    c0
    wne
    #
    @0
    vf
    cv
    cfv
    @0
    wcel
    #
    wi
    #
    vx
    cA
    wral
    #
    vf
    wex
    #
    @2
    vx
    cA
    wral
    #
    vf
    wex
    wph
    cA
    com
    cen
    wbr
    #
    @5
    axccd.1
    wph
    cA
    cvv
    wcel
    #
    @7
    @5
    wi
    #
    wph
    @7
    @8
    axccd.1
    @7
    @8
    com
    cvv
    wcel
    cA
    com
    encv
    simpld
    syl
    vy
    cv
    #
    com
    cen
    wbr
    #
    @3
    vx
    @10
    wral
    #
    vf
    wex
    #
    wi
    @9
    vy
    cA
    cvv
    @10
    cA
    wceq
    #
    @11
    @7
    @13
    @5
    @10
    cA
    com
    cen
    breq1
    @14
    @12
    @4
    vf
    @3
    vx
    @10
    cA
    raleq
    exbidv
    imbi12d
    vy
    vx
    vf
    ax-cc
    vtoclg
    syl
    mpd
    wph
    @4
    @6
    vf
    wph
    @4
    @6
    wph
    @4
    wa
    #
    @2
    vx
    cA
    wph
    @4
    vx
    wph
    vx
    nfv
    @3
    vx
    cA
    nfra1
    nfan
    @15
    @0
    cA
    wcel
    #
    @2
    @15
    @16
    wa
    @1
    @2
    wph
    @16
    @1
    @4
    axccd.2
    adantlr
    @4
    @16
    @3
    wph
    @3
    vx
    cA
    rspa
    adantll
    mpd
    ex
    ralrimi
    ex
    eximdv
    mpd
end
