include "cmul.mm"
include "co.mm"
include "cdiv.mm"
include "c1.mm"
include "mulcld.mm"
include "mulne0d.mm"
include "mulne0bbd.mm"
include "divcan7d.mm"
include "eqcomd.mm"
include "dividd.mm"
include "divcan4d.mm"
include "oveq12d.mm"
include "eqidd.mm"
include "3eqtrd.mm"

theorem divcan8d
  let wph: wff ph
  let cA: class A
  let cB: class B
  assume divcan8d.a: |- ( ph -> A e. CC )
  assume divcan8d.b: |- ( ph -> B e. CC )
  assume divcan8d.a0: |- ( ph -> A =/= 0 )
  assume divcan8d.b0: |- ( ph -> B =/= 0 )


  assert |- ( ph -> ( B / ( A x. B ) ) = ( 1 / A ) )

  proof
    wph
    cB
    cA
    cB
    cmul
    co
    #
    cdiv
    co
    #
    cB
    cB
    cdiv
    co
    #
    @0
    cB
    cdiv
    co
    #
    cdiv
    co
    #
    c1
    cA
    cdiv
    co
    #
    @5
    wph
    @4
    @1
    wph
    cB
    @0
    cB
    divcan8d.b
    wph
    cA
    cB
    divcan8d.a
    divcan8d.b
    mulcld
    divcan8d.b
    wph
    cA
    cB
    divcan8d.a
    divcan8d.b
    divcan8d.a0
    divcan8d.b0
    mulne0d
    #
    wph
    cA
    cB
    divcan8d.a
    divcan8d.b
    @6
    mulne0bbd
    divcan7d
    eqcomd
    wph
    @2
    c1
    @3
    cA
    cdiv
    wph
    cB
    divcan8d.b
    divcan8d.b0
    dividd
    wph
    cA
    cB
    divcan8d.a
    divcan8d.b
    divcan8d.b0
    divcan4d
    oveq12d
    wph
    @5
    eqidd
    3eqtrd
end
