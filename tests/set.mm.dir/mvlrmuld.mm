include "cmul.mm"
include "co.mm"
include "cdiv.mm"
include "divcan4d.mm"
include "oveq1d.mm"
include "eqtr3d.mm"

theorem mvlrmuld
  let wph: wff ph
  let cA: class A
  let cB: class B
  let cC: class C
  let vk: setvar k
  let vx: setvar x
  assume mvlrmuld.1: |- ( ph -> A e. CC )
  assume mvlrmuld.2: |- ( ph -> B e. CC )
  assume mvlrmuld.3: |- ( ph -> B =/= 0 )
  assume mvlrmuld.4: |- ( ph -> ( A x. B ) = C )


  assert |- ( ph -> A = ( C / B ) )

  proof
    wph
    cA
    cB
    cmul
    co
    #
    cB
    cdiv
    co
    cA
    cC
    cB
    cdiv
    co
    wph
    cA
    cB
    mvlrmuld.1
    mvlrmuld.2
    mvlrmuld.3
    divcan4d
    wph
    @0
    cC
    cB
    cdiv
    mvlrmuld.4
    oveq1d
    eqtr3d
end
