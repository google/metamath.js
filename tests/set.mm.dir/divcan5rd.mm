include "cmul.mm"
include "co.mm"
include "cdiv.mm"
include "mulcomd.mm"
include "oveq12d.mm"
include "divcan5d.mm"
include "eqtrd.mm"

theorem divcan5rd
  let wph: wff ph
  let cA: class A
  let cB: class B
  let cC: class C
  assume div1d.1: |- ( ph -> A e. CC )
  assume divcld.2: |- ( ph -> B e. CC )
  assume divmuld.3: |- ( ph -> C e. CC )
  assume divmuld.4: |- ( ph -> B =/= 0 )
  assume divdiv23d.5: |- ( ph -> C =/= 0 )


  assert |- ( ph -> ( ( A x. C ) / ( B x. C ) ) = ( A / B ) )

  proof
    wph
    cA
    cC
    cmul
    co
    #
    cB
    cC
    cmul
    co
    #
    cdiv
    co
    cC
    cA
    cmul
    co
    #
    cC
    cB
    cmul
    co
    #
    cdiv
    co
    cA
    cB
    cdiv
    co
    wph
    @0
    @2
    @1
    @3
    cdiv
    wph
    cA
    cC
    div1d.1
    divmuld.3
    mulcomd
    wph
    cB
    cC
    divcld.2
    divmuld.3
    mulcomd
    oveq12d
    wph
    cA
    cB
    cC
    div1d.1
    divcld.2
    divmuld.3
    divmuld.4
    divdiv23d.5
    divcan5d
    eqtrd
end
