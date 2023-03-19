include "wcel.mm"
include "wa.mm"
include "ccom.mm"
include "wbr.mm"
include "cv.mm"
include "wex.mm"
include "cop.mm"
include "brcog.mm"
include "df-br.mm"
include "anbi12i.mm"
include "exbii.mm"
include "3bitr3g.mm"

theorem opelco2g
  let vx: setvar x
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D
  let cV: class V
  let cW: class W
  let vy: setvar y
  let vz: setvar z

  disjoint A x
  disjoint B x
  disjoint C x
  disjoint D x
  disjoint x y
  disjoint x z
  disjoint y z
  disjoint A y
  disjoint A z
  disjoint B y
  disjoint B z
  disjoint C y
  disjoint C z
  disjoint D y
  disjoint D z
  assert |- ( ( A e. V /\ B e. W ) -> ( <. A , B >. e. ( C o. D ) <-> E. x ( <. A , x >. e. D /\ <. x , B >. e. C ) ) )

  proof
    cA
    cV
    wcel
    cB
    cW
    wcel
    wa
    cA
    cB
    cC
    cD
    ccom
    #
    wbr
    cA
    vx
    cv
    #
    cD
    wbr
    #
    @1
    cB
    cC
    wbr
    #
    wa
    #
    vx
    wex
    cA
    cB
    cop
    @0
    wcel
    cA
    @1
    cop
    cD
    wcel
    #
    @1
    cB
    cop
    cC
    wcel
    #
    wa
    #
    vx
    wex
    vx
    cA
    cB
    cC
    cD
    cV
    cW
    brcog
    cA
    cB
    @0
    df-br
    @4
    @7
    vx
    @2
    @5
    @3
    @6
    cA
    @1
    cD
    df-br
    @1
    cB
    cC
    df-br
    anbi12i
    exbii
    3bitr3g
end
