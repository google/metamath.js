include "cmin.mm"
include "co.mm"
include "cneg.mm"
include "negsubdi2d.mm"
include "neg2subd.mm"
include "eqtr4d.mm"

theorem negsubdi3d
  let wph: wff ph
  let cA: class A
  let cB: class B
  assume negsubdi3d.1: |- ( ph -> A e. CC )
  assume negsubdi3d.2: |- ( ph -> B e. CC )


  assert |- ( ph -> -u ( A - B ) = ( -u A - -u B ) )

  proof
    wph
    cA
    cB
    cmin
    co
    cneg
    cB
    cA
    cmin
    co
    cA
    cneg
    cB
    cneg
    cmin
    co
    wph
    cA
    cB
    negsubdi3d.1
    negsubdi3d.2
    negsubdi2d
    wph
    cA
    cB
    negsubdi3d.1
    negsubdi3d.2
    neg2subd
    eqtr4d
end
