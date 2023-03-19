include "cmul.mm"
include "co.mm"
include "wceq.mm"
include "cdiv.mm"
include "oveq1.mm"
include "divcan4d.mm"
include "eqeq1d.mm"
include "syl5ib.mm"
include "divcan1d.mm"
include "eqeq2d.mm"
include "impbid.mm"

theorem bj-ldiv
  let wph: wff ph
  let cA: class A
  let cB: class B
  let cC: class C
  assume bj-ldiv.a: |- ( ph -> A e. CC )
  assume bj-ldiv.b: |- ( ph -> B e. CC )
  assume bj-ldiv.c: |- ( ph -> C e. CC )
  assume bj-ldiv.bn0: |- ( ph -> B =/= 0 )


  assert |- ( ph -> ( ( A x. B ) = C <-> A = ( C / B ) ) )

  proof
    wph
    cA
    cB
    cmul
    co
    #
    cC
    wceq
    #
    cA
    cC
    cB
    cdiv
    co
    #
    wceq
    #
    @1
    @0
    cB
    cdiv
    co
    #
    @2
    wceq
    wph
    @3
    @0
    cC
    cB
    cdiv
    oveq1
    wph
    @4
    cA
    @2
    wph
    cA
    cB
    bj-ldiv.a
    bj-ldiv.b
    bj-ldiv.bn0
    divcan4d
    eqeq1d
    syl5ib
    @3
    @0
    @2
    cB
    cmul
    co
    #
    wceq
    wph
    @1
    cA
    @2
    cB
    cmul
    oveq1
    wph
    @5
    cC
    @0
    wph
    cC
    cB
    bj-ldiv.c
    bj-ldiv.b
    bj-ldiv.bn0
    divcan1d
    eqeq2d
    syl5ib
    impbid
end
