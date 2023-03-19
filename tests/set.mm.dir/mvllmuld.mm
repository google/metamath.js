include "cmul.mm"
include "co.mm"
include "cdiv.mm"
include "divcan4d.mm"
include "mulcomd.mm"
include "eqtr3d.mm"
include "oveq1d.mm"

theorem mvllmuld
  let wph: wff ph
  let cA: class A
  let cB: class B
  let cC: class C
  assume mvllmuld.1: |- ( ph -> A e. CC )
  assume mvllmuld.2: |- ( ph -> B e. CC )
  assume mvllmuld.3: |- ( ph -> A =/= 0 )
  assume mvllmuld.4: |- ( ph -> ( A x. B ) = C )


  assert |- ( ph -> B = ( C / A ) )

  proof
    wph
    cB
    cA
    cmul
    co
    #
    cA
    cdiv
    co
    cB
    cC
    cA
    cdiv
    co
    wph
    cB
    cA
    mvllmuld.2
    mvllmuld.1
    mvllmuld.3
    divcan4d
    wph
    @0
    cC
    cA
    cdiv
    wph
    cA
    cB
    cmul
    co
    @0
    cC
    wph
    cA
    cB
    mvllmuld.1
    mvllmuld.2
    mulcomd
    mvllmuld.4
    eqtr3d
    oveq1d
    eqtr3d
end
