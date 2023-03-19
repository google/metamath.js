include "cc.mm"
include "wcel.mm"
include "cabs.mm"
include "cfv.mm"
include "cmin.mm"
include "co.mm"
include "cle.mm"
include "wbr.mm"
include "abs2difabs.mm"
include "syl2anc.mm"

theorem abs2difabsd
  let wph: wff ph
  let cA: class A
  let cB: class B
  assume abscld.1: |- ( ph -> A e. CC )
  assume abssubd.2: |- ( ph -> B e. CC )


  assert |- ( ph -> ( abs ` ( ( abs ` A ) - ( abs ` B ) ) ) <_ ( abs ` ( A - B ) ) )

  proof
    wph
    cA
    cc
    wcel
    cB
    cc
    wcel
    cA
    cabs
    cfv
    cB
    cabs
    cfv
    cmin
    co
    cabs
    cfv
    cA
    cB
    cmin
    co
    cabs
    cfv
    cle
    wbr
    abscld.1
    abssubd.2
    cA
    cB
    abs2difabs
    syl2anc
end
