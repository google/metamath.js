include "cdiv.mm"
include "co.mm"
include "cmul.mm"
include "mulcld.mm"
include "div32d.mm"
include "divcan3d.mm"
include "oveq2d.mm"
include "eqidd.mm"
include "3eqtrd.mm"

theorem dmmcand
  let wph: wff ph
  let cA: class A
  let cB: class B
  let cC: class C
  assume dmmcand.a: |- ( ph -> A e. CC )
  assume dmmcand.b: |- ( ph -> B e. CC )
  assume dmmcand.c: |- ( ph -> C e. CC )
  assume dmmcand.bn0: |- ( ph -> B =/= 0 )


  assert |- ( ph -> ( ( A / B ) x. ( B x. C ) ) = ( A x. C ) )

  proof
    wph
    cA
    cB
    cdiv
    co
    cB
    cC
    cmul
    co
    #
    cmul
    co
    cA
    @0
    cB
    cdiv
    co
    #
    cmul
    co
    cA
    cC
    cmul
    co
    #
    @2
    wph
    cA
    cB
    @0
    dmmcand.a
    dmmcand.b
    wph
    cB
    cC
    dmmcand.b
    dmmcand.c
    mulcld
    dmmcand.bn0
    div32d
    wph
    @1
    cC
    cA
    cmul
    wph
    cC
    cB
    dmmcand.c
    dmmcand.b
    dmmcand.bn0
    divcan3d
    oveq2d
    wph
    @2
    eqidd
    3eqtrd
end
