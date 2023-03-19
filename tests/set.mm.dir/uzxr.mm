include "cuz.mm"
include "cfv.mm"
include "wcel.mm"
include "eqid.mm"
include "id.mm"
include "uzxrd.mm"

theorem uzxr
  let cA: class A
  let cM: class M


  assert |- ( A e. ( ZZ>= ` M ) -> A e. RR* )

  proof
    cA
    cM
    cuz
    cfv
    #
    wcel
    #
    cA
    cM
    @0
    @0
    eqid
    @1
    id
    uzxrd
end
