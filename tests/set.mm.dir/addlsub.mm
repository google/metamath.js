include "caddc.mm"
include "co.mm"
include "wceq.mm"
include "cmin.mm"
include "oveq1.mm"
include "pncand.mm"
include "wa.mm"
include "wi.mm"
include "eqtr2.mm"
include "eqcomd.mm"
include "a1i.mm"
include "mpan2d.mm"
include "syl5.mm"
include "npcand.mm"
include "eqtr.mm"
include "impbid.mm"

theorem addlsub
  let wph: wff ph
  let cA: class A
  let cB: class B
  let cC: class C
  assume addlsub.a: |- ( ph -> A e. CC )
  assume addlsub.b: |- ( ph -> B e. CC )
  assume addlsub.c: |- ( ph -> C e. CC )


  assert |- ( ph -> ( ( A + B ) = C <-> A = ( C - B ) ) )

  proof
    wph
    cA
    cB
    caddc
    co
    #
    cC
    wceq
    #
    cA
    cC
    cB
    cmin
    co
    #
    wceq
    #
    @1
    @0
    cB
    cmin
    co
    #
    @2
    wceq
    #
    wph
    @3
    @0
    cC
    cB
    cmin
    oveq1
    wph
    @5
    @4
    cA
    wceq
    #
    @3
    wph
    cA
    cB
    addlsub.a
    addlsub.b
    pncand
    @5
    @6
    wa
    #
    @3
    wi
    wph
    @7
    @2
    cA
    @4
    @2
    cA
    eqtr2
    eqcomd
    a1i
    mpan2d
    syl5
    @3
    @0
    @2
    cB
    caddc
    co
    #
    wceq
    #
    wph
    @1
    cA
    @2
    cB
    caddc
    oveq1
    wph
    @9
    @8
    cC
    wceq
    #
    @1
    wph
    cC
    cB
    addlsub.c
    addlsub.b
    npcand
    @9
    @10
    wa
    @1
    wi
    wph
    @0
    @8
    cC
    eqtr
    a1i
    mpan2d
    syl5
    impbid
end
