include "wceq.mm"
include "wa.mm"
include "simpr.mm"
include "biimpa.mm"
include "eqtr4d.mm"
include "wn.mm"
include "cpr.mm"
include "wcel.mm"
include "wo.mm"
include "elpri.mm"
include "syl.mm"
include "orcanai.mm"
include "simpl.mm"
include "notbid.mm"
include "wi.mm"
include "pm2.53.mm"
include "3syl.mm"
include "sylc.mm"
include "pm2.61dan.mm"

theorem elpreq
  let wph: wff ph
  let cA: class A
  let cB: class B
  let cX: class X
  let cY: class Y
  assume elpreq.1: |- ( ph -> X e. { A , B } )
  assume elpreq.2: |- ( ph -> Y e. { A , B } )
  assume elpreq.3: |- ( ph -> ( X = A <-> Y = A ) )


  assert |- ( ph -> X = Y )

  proof
    wph
    cX
    cA
    wceq
    #
    cX
    cY
    wceq
    wph
    @0
    wa
    cX
    cA
    cY
    wph
    @0
    simpr
    wph
    @0
    cY
    cA
    wceq
    #
    elpreq.3
    biimpa
    eqtr4d
    wph
    @0
    wn
    #
    wa
    #
    cX
    cB
    cY
    wph
    @0
    cX
    cB
    wceq
    #
    wph
    cX
    cA
    cB
    cpr
    #
    wcel
    @0
    @4
    wo
    elpreq.1
    cX
    cA
    cB
    elpri
    syl
    orcanai
    @3
    wph
    @1
    wn
    #
    cY
    cB
    wceq
    #
    wph
    @2
    simpl
    wph
    @2
    @6
    wph
    @0
    @1
    elpreq.3
    notbid
    biimpa
    wph
    cY
    @5
    wcel
    @1
    @7
    wo
    @6
    @7
    wi
    elpreq.2
    cY
    cA
    cB
    elpri
    @1
    @7
    pm2.53
    3syl
    sylc
    eqtr4d
    pm2.61dan
end
