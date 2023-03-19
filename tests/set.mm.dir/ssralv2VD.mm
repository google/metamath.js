include "wss.mm"
include "wa.mm"
include "wral.mm"
include "wi.mm"
include "cv.mm"
include "wcel.mm"
include "wal.mm"
include "ax-5.mm"
include "hbra1.mm"
include "idn1.mm"
include "simpr.mm"
include "e1a.mm"
include "idn3.mm"
include "simpl.mm"
include "idn2.mm"
include "ssralv.mm"
include "e12.mm"
include "df-ral.mm"
include "biimpi.mm"
include "e2.mm"
include "sp.mm"
include "pm2.27.mm"
include "e32.mm"
include "e13.mm"
include "in3.mm"
include "gen21nv.mm"
include "biimpri.mm"
include "in2.mm"
include "in1.mm"

theorem ssralv2VD
  let wph: wff ph
  let vx: setvar x
  let vy: setvar y
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D

  disjoint A x
  disjoint B x
  disjoint C x
  disjoint C y
  disjoint D x
  disjoint D y
  assert |- ( ( A C_ B /\ C C_ D ) -> ( A. x e. B A. y e. D ph -> A. x e. A A. y e. C ph ) )

  proof
    cA
    cB
    wss
    #
    cC
    cD
    wss
    #
    wa
    #
    wph
    vy
    cD
    wral
    #
    vx
    cB
    wral
    #
    wph
    vy
    cC
    wral
    #
    vx
    cA
    wral
    #
    wi
    @2
    @4
    @6
    @2
    @4
    vx
    cv
    cA
    wcel
    #
    @5
    wi
    #
    vx
    wal
    #
    @6
    @2
    @4
    @8
    vx
    @2
    vx
    ax-5
    @3
    vx
    cB
    hbra1
    @2
    @4
    @7
    @5
    @2
    @1
    @4
    @7
    @3
    @5
    @2
    @2
    @1
    @2
    idn1
    #
    @0
    @1
    simpr
    e1a
    @2
    @4
    @7
    @7
    @7
    @3
    wi
    #
    @3
    @2
    @4
    @7
    idn3
    @2
    @4
    @11
    vx
    wal
    #
    @11
    @2
    @4
    @3
    vx
    cA
    wral
    #
    @12
    @2
    @0
    @4
    @4
    @13
    @2
    @2
    @0
    @10
    @0
    @1
    simpl
    e1a
    @2
    @4
    idn2
    @3
    vx
    cA
    cB
    ssralv
    e12
    @13
    @12
    @3
    vx
    cA
    df-ral
    biimpi
    e2
    @11
    vx
    sp
    e2
    @7
    @3
    pm2.27
    e32
    wph
    vy
    cC
    cD
    ssralv
    e13
    in3
    gen21nv
    @6
    @9
    @5
    vx
    cA
    df-ral
    biimpri
    e2
    in2
    in1
end
