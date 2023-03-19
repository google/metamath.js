include "wcel.mm"
include "wa.mm"
include "simpl.mm"
include "simpr.mm"
include "s2cld.mm"

theorem s2cl
  let cA: class A
  let cB: class B
  let cX: class X


  assert |- ( ( A e. X /\ B e. X ) -> <" A B "> e. Word X )

  proof
    cA
    cX
    wcel
    #
    cB
    cX
    wcel
    #
    wa
    cA
    cB
    cX
    @0
    @1
    simpl
    @0
    @1
    simpr
    s2cld
end
