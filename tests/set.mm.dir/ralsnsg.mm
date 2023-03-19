include "wcel.mm"
include "wsbc.mm"
include "cv.mm"
include "wceq.mm"
include "wi.mm"
include "wal.mm"
include "csn.mm"
include "wral.mm"
include "sbc6g.mm"
include "df-ral.mm"
include "velsn.mm"
include "imbi1i.mm"
include "albii.mm"
include "bitri.mm"
include "syl6rbbr.mm"

theorem ralsnsg
  let wph: wff ph
  let vx: setvar x
  let cA: class A
  let cV: class V
  let wps: wff ps

  disjoint A x
  disjoint ps x
  assert |- ( A e. V -> ( A. x e. { A } ph <-> [. A / x ]. ph ) )

  proof
    cA
    cV
    wcel
    wph
    vx
    cA
    wsbc
    vx
    cv
    #
    cA
    wceq
    #
    wph
    wi
    #
    vx
    wal
    #
    wph
    vx
    cA
    csn
    #
    wral
    #
    wph
    vx
    cA
    cV
    sbc6g
    @5
    @0
    @4
    wcel
    #
    wph
    wi
    #
    vx
    wal
    @3
    wph
    vx
    @4
    df-ral
    @7
    @2
    vx
    @6
    @1
    wph
    vx
    cA
    velsn
    imbi1i
    albii
    bitri
    syl6rbbr
end
