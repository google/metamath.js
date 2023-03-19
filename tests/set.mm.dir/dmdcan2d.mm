include "cdiv.mm"
include "co.mm"
include "cmul.mm"
include "divcld.mm"
include "mulcomd.mm"
include "dmdcand.mm"
include "eqtrd.mm"

theorem dmdcan2d
  let wph: wff ph
  let cA: class A
  let cB: class B
  let cC: class C
  assume div1d.1: |- ( ph -> A e. CC )
  assume divcld.2: |- ( ph -> B e. CC )
  assume divmuld.3: |- ( ph -> C e. CC )
  assume divmuld.4: |- ( ph -> B =/= 0 )
  assume divdiv23d.5: |- ( ph -> C =/= 0 )


  assert |- ( ph -> ( ( A / B ) x. ( B / C ) ) = ( A / C ) )

  proof
    wph
    cA
    cB
    cdiv
    co
    #
    cB
    cC
    cdiv
    co
    #
    cmul
    co
    @1
    @0
    cmul
    co
    cA
    cC
    cdiv
    co
    wph
    @0
    @1
    wph
    cA
    cB
    div1d.1
    divcld.2
    divmuld.4
    divcld
    wph
    cB
    cC
    divcld.2
    divmuld.3
    divdiv23d.5
    divcld
    mulcomd
    wph
    cA
    cB
    cC
    div1d.1
    divcld.2
    divmuld.3
    divmuld.4
    divdiv23d.5
    dmdcand
    eqtrd
end
