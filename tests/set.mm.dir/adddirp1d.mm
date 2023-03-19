include "c1.mm"
include "caddc.mm"
include "co.mm"
include "cmul.mm"
include "1cnd.mm"
include "adddird.mm"
include "mulid2d.mm"
include "oveq2d.mm"
include "eqtrd.mm"

theorem adddirp1d
  let wph: wff ph
  let cA: class A
  let cB: class B
  assume adddirp1d.a: |- ( ph -> A e. CC )
  assume adddirp1d.b: |- ( ph -> B e. CC )


  assert |- ( ph -> ( ( A + 1 ) x. B ) = ( ( A x. B ) + B ) )

  proof
    wph
    cA
    c1
    caddc
    co
    cB
    cmul
    co
    cA
    cB
    cmul
    co
    #
    c1
    cB
    cmul
    co
    #
    caddc
    co
    @0
    cB
    caddc
    co
    wph
    cA
    c1
    cB
    adddirp1d.a
    wph
    1cnd
    adddirp1d.b
    adddird
    wph
    @1
    cB
    @0
    caddc
    wph
    cB
    adddirp1d.b
    mulid2d
    oveq2d
    eqtrd
end
