include "cres.mm"
include "crn.mm"
include "wss.mm"
include "wcel.mm"
include "wn.mm"
include "rnresss.mm"
include "ssnel.mm"
include "mpan.mm"

theorem nelrnres
  let cA: class A
  let cB: class B
  let cC: class C


  assert |- ( -. A e. ran B -> -. A e. ran ( B |` C ) )

  proof
    cB
    cC
    cres
    crn
    #
    cB
    crn
    #
    wss
    cA
    @1
    wcel
    wn
    cA
    @0
    wcel
    wn
    cB
    cC
    rnresss
    @0
    @1
    cA
    ssnel
    mpan
end
