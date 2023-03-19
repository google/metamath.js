include "cmin.mm"
include "co.mm"
include "caddc.mm"
include "subcld.mm"
include "addcld.mm"
include "subsub2d.mm"
include "pncand.mm"
include "eqtr3d.mm"

theorem pnpncand
  let wph: wff ph
  let cA: class A
  let cB: class B
  let cC: class C
  assume pnpncand.1: |- ( ph -> A e. CC )
  assume pnpncand.2: |- ( ph -> B e. CC )
  assume pnpncand.3: |- ( ph -> C e. CC )


  assert |- ( ph -> ( ( A + ( B - C ) ) + ( C - B ) ) = A )

  proof
    wph
    cA
    cB
    cC
    cmin
    co
    #
    caddc
    co
    #
    @0
    cmin
    co
    @1
    cC
    cB
    cmin
    co
    caddc
    co
    cA
    wph
    @1
    cB
    cC
    wph
    cA
    @0
    pnpncand.1
    wph
    cB
    cC
    pnpncand.2
    pnpncand.3
    subcld
    #
    addcld
    pnpncand.2
    pnpncand.3
    subsub2d
    wph
    cA
    @0
    pnpncand.1
    @2
    pncand
    eqtr3d
end
