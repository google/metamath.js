include "wcel.mm"
include "cvv.mm"
include "elex.mm"
include "wa.mm"
include "wrex.mm"
include "adantr.mm"
include "wi.mm"
include "wral.mm"
include "nfv.mm"
include "cv.mm"
include "imp.mm"
include "adantrl.mm"
include "wceq.mm"
include "wb.mm"
include "riotasvd.mm"
include "impr.mm"
include "eqcomd.mm"
include "syldan.mm"
include "mpbid.mm"
include "exp45.mm"
include "ralrimd.mm"
include "wnf.mm"
include "r19.23t.mm"
include "syl.mm"
include "sylibd.mm"
include "mpd.mm"
include "sylan2.mm"

theorem riotasv3d
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let wth: wff th
  let vx: setvar x
  let vy: setvar y
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D
  let cV: class V
  assume riotasv3d.1: |- F/ y ph
  assume riotasv3d.2: |- ( ph -> F/ y th )
  assume riotasv3d.3: |- ( ph -> D = ( iota_ x e. A A. y e. B ( ps -> x = C ) ) )
  assume riotasv3d.4: |- ( ( ph /\ C = D ) -> ( ch <-> th ) )
  assume riotasv3d.5: |- ( ph -> ( ( y e. B /\ ps ) -> ch ) )
  assume riotasv3d.6: |- ( ph -> D e. A )
  assume riotasv3d.7: |- ( ph -> E. y e. B ps )

  disjoint x y
  disjoint A x
  disjoint A y
  disjoint B x
  disjoint C x
  disjoint ps x
  assert |- ( ( ph /\ A e. V ) -> th )

  proof
    cA
    cV
    wcel
    wph
    cA
    cvv
    wcel
    #
    wth
    cA
    cV
    elex
    wph
    @0
    wa
    wps
    vy
    cB
    wrex
    #
    wth
    wph
    @1
    @0
    riotasv3d.7
    adantr
    wph
    @0
    @1
    wth
    wi
    #
    wph
    @0
    wps
    wth
    wi
    #
    vy
    cB
    wral
    #
    @2
    wph
    @0
    @3
    vy
    cB
    riotasv3d.1
    @0
    vy
    nfv
    wph
    @0
    vy
    cv
    cB
    wcel
    #
    wps
    wth
    wph
    @0
    @5
    wps
    wa
    #
    wa
    #
    wa
    #
    wch
    wth
    wph
    @6
    wch
    @0
    wph
    @6
    wch
    riotasv3d.5
    imp
    adantrl
    wph
    @7
    cC
    cD
    wceq
    wch
    wth
    wb
    @8
    cD
    cC
    wph
    @0
    @6
    cD
    cC
    wceq
    wph
    wps
    vx
    vy
    cA
    cB
    cC
    cD
    cvv
    riotasv3d.3
    riotasv3d.6
    riotasvd
    impr
    eqcomd
    riotasv3d.4
    syldan
    mpbid
    exp45
    ralrimd
    wph
    wth
    vy
    wnf
    @4
    @2
    wb
    riotasv3d.2
    wps
    wth
    vy
    cB
    r19.23t
    syl
    sylibd
    imp
    mpd
    sylan2
end
