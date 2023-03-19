include "wral.mm"
include "cdif.mm"
include "cun.mm"
include "wa.mm"
include "biantrud.mm"
include "ralunb.mm"
include "syl6bbr.mm"
include "wss.mm"
include "wceq.mm"
include "undif.mm"
include "sylib.mm"
include "raleqdv.mm"
include "bitrd.mm"

theorem raldifeq
  let wph: wff ph
  let wps: wff ps
  let vx: setvar x
  let cA: class A
  let cB: class B
  assume raldifeq.1: |- ( ph -> A C_ B )
  assume raldifeq.2: |- ( ph -> A. x e. ( B \ A ) ps )

  disjoint A x
  disjoint B x
  assert |- ( ph -> ( A. x e. A ps <-> A. x e. B ps ) )

  proof
    wph
    wps
    vx
    cA
    wral
    #
    wps
    vx
    cA
    cB
    cA
    cdif
    #
    cun
    #
    wral
    #
    wps
    vx
    cB
    wral
    wph
    @0
    @0
    wps
    vx
    @1
    wral
    #
    wa
    @3
    wph
    @4
    @0
    raldifeq.2
    biantrud
    wps
    vx
    cA
    @1
    ralunb
    syl6bbr
    wph
    wps
    vx
    @2
    cB
    wph
    cA
    cB
    wss
    @2
    cB
    wceq
    raldifeq.1
    cA
    cB
    undif
    sylib
    raleqdv
    bitrd
end
