include "wcel.mm"
include "w3a.mm"
include "simp1.mm"
include "simp2.mm"
include "simp3.mm"
include "s3cld.mm"

theorem s3cl
  let cA: class A
  let cB: class B
  let cC: class C
  let cX: class X


  assert |- ( ( A e. X /\ B e. X /\ C e. X ) -> <" A B C "> e. Word X )

  proof
    cA
    cX
    wcel
    #
    cB
    cX
    wcel
    #
    cC
    cX
    wcel
    #
    w3a
    cA
    cB
    cC
    cX
    @0
    @1
    @2
    simp1
    @0
    @1
    @2
    simp2
    @0
    @1
    @2
    simp3
    s3cld
end
