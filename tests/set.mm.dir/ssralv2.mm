include "wss.mm"
include "wa.mm"
include "wral.mm"
include "nfv.mm"
include "nfra1.mm"
include "cv.mm"
include "wcel.mm"
include "wi.mm"
include "wal.mm"
include "ssralv.mm"
include "adantr.mm"
include "df-ral.mm"
include "syl6ib.mm"
include "sp.mm"
include "syl6.mm"
include "adantl.mm"
include "syl6d.mm"
include "ralrimd.mm"

theorem ssralv2
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
    @2
    vx
    nfv
    @3
    vx
    cB
    nfra1
    @2
    @4
    vx
    cv
    cA
    wcel
    #
    @3
    @5
    @2
    @4
    @6
    @3
    wi
    #
    vx
    wal
    #
    @7
    @2
    @4
    @3
    vx
    cA
    wral
    #
    @8
    @0
    @4
    @9
    wi
    @1
    @3
    vx
    cA
    cB
    ssralv
    adantr
    @3
    vx
    cA
    df-ral
    syl6ib
    @7
    vx
    sp
    syl6
    @1
    @3
    @5
    wi
    @0
    wph
    vy
    cC
    cD
    ssralv
    adantl
    syl6d
    ralrimd
end
