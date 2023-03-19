include "wpss.mm"
include "cen.mm"
include "wbr.mm"
include "cfn.mm"
include "wcel.mm"
include "wn.mm"
include "csdm.mm"
include "php3.mm"
include "ex.mm"
include "sdomnen.mm"
include "syl6com.mm"
include "con2d.mm"
include "imp.mm"

theorem pssinf
  let cA: class A
  let cB: class B


  assert |- ( ( A C. B /\ A ~~ B ) -> -. B e. Fin )

  proof
    cA
    cB
    wpss
    #
    cA
    cB
    cen
    wbr
    #
    cB
    cfn
    wcel
    #
    wn
    @0
    @2
    @1
    @2
    @0
    cA
    cB
    csdm
    wbr
    #
    @1
    wn
    @2
    @0
    @3
    cB
    cA
    php3
    ex
    cA
    cB
    sdomnen
    syl6com
    con2d
    imp
end
