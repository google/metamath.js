include "wcel.mm"
include "cdif.mm"
include "wn.mm"
include "eldif.mm"
include "simplbi2.mm"
include "con1d.mm"
include "imp.mm"

theorem neldif
  let cA: class A
  let cB: class B
  let cC: class C


  assert |- ( ( A e. B /\ -. A e. ( B \ C ) ) -> A e. C )

  proof
    cA
    cB
    wcel
    #
    cA
    cB
    cC
    cdif
    wcel
    #
    wn
    cA
    cC
    wcel
    #
    @0
    @2
    @1
    @1
    @0
    @2
    wn
    cA
    cB
    cC
    eldif
    simplbi2
    con1d
    imp
end
