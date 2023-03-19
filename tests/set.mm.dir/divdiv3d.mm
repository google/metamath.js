include "cdiv.mm"
include "co.mm"
include "cmul.mm"
include "divdiv1d.mm"
include "mulcomd.mm"
include "oveq2d.mm"
include "eqtrd.mm"

theorem divdiv3d
  let wph: wff ph
  let cA: class A
  let cB: class B
  let cC: class C
  assume divdiv3d.1: |- ( ph -> A e. CC )
  assume divdiv3d.2: |- ( ph -> B e. CC )
  assume divdiv3d.3: |- ( ph -> C e. CC )
  assume divdiv3d.4: |- ( ph -> B =/= 0 )
  assume divdiv3d.5: |- ( ph -> C =/= 0 )


  assert |- ( ph -> ( ( A / B ) / C ) = ( A / ( C x. B ) ) )

  proof
    wph
    cA
    cB
    cdiv
    co
    cC
    cdiv
    co
    cA
    cB
    cC
    cmul
    co
    #
    cdiv
    co
    cA
    cC
    cB
    cmul
    co
    #
    cdiv
    co
    wph
    cA
    cB
    cC
    divdiv3d.1
    divdiv3d.2
    divdiv3d.3
    divdiv3d.4
    divdiv3d.5
    divdiv1d
    wph
    @0
    @1
    cA
    cdiv
    wph
    cB
    cC
    divdiv3d.2
    divdiv3d.3
    mulcomd
    oveq2d
    eqtrd
end
