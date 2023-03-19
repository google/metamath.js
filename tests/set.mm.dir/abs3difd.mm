include "cc.mm"
include "wcel.mm"
include "cmin.mm"
include "co.mm"
include "cabs.mm"
include "cfv.mm"
include "caddc.mm"
include "cle.mm"
include "wbr.mm"
include "abs3dif.mm"
include "syl3anc.mm"

theorem abs3difd
  let wph: wff ph
  let cA: class A
  let cB: class B
  let cC: class C
  assume abscld.1: |- ( ph -> A e. CC )
  assume abssubd.2: |- ( ph -> B e. CC )
  assume abs3difd.3: |- ( ph -> C e. CC )


  assert |- ( ph -> ( abs ` ( A - B ) ) <_ ( ( abs ` ( A - C ) ) + ( abs ` ( C - B ) ) ) )

  proof
    wph
    cA
    cc
    wcel
    cB
    cc
    wcel
    cC
    cc
    wcel
    cA
    cB
    cmin
    co
    cabs
    cfv
    cA
    cC
    cmin
    co
    cabs
    cfv
    cC
    cB
    cmin
    co
    cabs
    cfv
    caddc
    co
    cle
    wbr
    abscld.1
    abssubd.2
    abs3difd.3
    cA
    cB
    cC
    abs3dif
    syl3anc
end
