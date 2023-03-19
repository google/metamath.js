include "cc.mm"
include "wcel.mm"
include "caddc.mm"
include "co.mm"
include "cabs.mm"
include "cfv.mm"
include "c2.mm"
include "cexp.mm"
include "ccj.mm"
include "cmul.mm"
include "cre.mm"
include "wceq.mm"
include "sqabsadd.mm"
include "mp2an.mm"

theorem sqabsaddi
  let cA: class A
  let cB: class B
  assume absvalsqi.1: |- A e. CC
  assume abssub.2: |- B e. CC


  assert |- ( ( abs ` ( A + B ) ) ^ 2 ) = ( ( ( ( abs ` A ) ^ 2 ) + ( ( abs ` B ) ^ 2 ) ) + ( 2 x. ( Re ` ( A x. ( * ` B ) ) ) ) )

  proof
    cA
    cc
    wcel
    cB
    cc
    wcel
    cA
    cB
    caddc
    co
    cabs
    cfv
    c2
    cexp
    co
    cA
    cabs
    cfv
    c2
    cexp
    co
    cB
    cabs
    cfv
    c2
    cexp
    co
    caddc
    co
    c2
    cA
    cB
    ccj
    cfv
    cmul
    co
    cre
    cfv
    cmul
    co
    caddc
    co
    wceq
    absvalsqi.1
    abssub.2
    cA
    cB
    sqabsadd
    mp2an
end
