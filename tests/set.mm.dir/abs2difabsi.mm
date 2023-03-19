include "cc.mm"
include "wcel.mm"
include "cabs.mm"
include "cfv.mm"
include "cmin.mm"
include "co.mm"
include "cle.mm"
include "wbr.mm"
include "abs2difabs.mm"
include "mp2an.mm"

theorem abs2difabsi
  let cA: class A
  let cB: class B
  assume abs2difabsi.1: |- A e. CC
  assume abs2difabsi.2: |- B e. CC


  assert |- ( abs ` ( ( abs ` A ) - ( abs ` B ) ) ) <_ ( abs ` ( A - B ) )

  proof
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
    abs2difabsi.1
    abs2difabsi.2
    cA
    cB
    abs2difabs
    mp2an
end
