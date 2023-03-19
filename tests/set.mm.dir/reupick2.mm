include "wi.mm"
include "wral.mm"
include "wrex.mm"
include "wreu.mm"
include "w3a.mm"
include "cv.mm"
include "wcel.mm"
include "wa.mm"
include "ancr.mm"
include "ralimi.mm"
include "rexim.mm"
include "syl.mm"
include "reupick3.mm"
include "3exp.mm"
include "com12.mm"
include "syl6.mm"
include "3imp1.mm"
include "rsp.mm"
include "3ad2ant1.mm"
include "imp.mm"
include "impbid.mm"

theorem reupick2
  let wph: wff ph
  let wps: wff ps
  let vx: setvar x
  let cA: class A
  let cB: class B

  disjoint A x
  disjoint B x
  assert |- ( ( ( A. x e. A ( ps -> ph ) /\ E. x e. A ps /\ E! x e. A ph ) /\ x e. A ) -> ( ph <-> ps ) )

  proof
    wps
    wph
    wi
    #
    vx
    cA
    wral
    #
    wps
    vx
    cA
    wrex
    #
    wph
    vx
    cA
    wreu
    #
    w3a
    #
    vx
    cv
    cA
    wcel
    #
    wa
    wph
    wps
    @1
    @2
    @3
    @5
    wph
    wps
    wi
    #
    @1
    @2
    wph
    wps
    wa
    #
    vx
    cA
    wrex
    #
    @3
    @5
    @6
    wi
    #
    wi
    @1
    wps
    @7
    wi
    #
    vx
    cA
    wral
    @2
    @8
    wi
    @0
    @10
    vx
    cA
    wps
    wph
    ancr
    ralimi
    wps
    @7
    vx
    cA
    rexim
    syl
    @3
    @8
    @9
    @3
    @8
    @5
    @6
    wph
    wps
    vx
    cA
    reupick3
    3exp
    com12
    syl6
    3imp1
    @4
    @5
    @0
    @1
    @2
    @5
    @0
    wi
    @3
    @0
    vx
    cA
    rsp
    3ad2ant1
    imp
    impbid
end
