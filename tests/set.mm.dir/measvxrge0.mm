include "cmeas.mm"
include "cfv.mm"
include "wcel.mm"
include "cc0.mm"
include "cpnf.mm"
include "cicc.mm"
include "co.mm"
include "measfrge0.mm"
include "ffvelrnda.mm"

theorem measvxrge0
  let cA: class A
  let cS: class S
  let cM: class M


  assert |- ( ( M e. ( measures ` S ) /\ A e. S ) -> ( M ` A ) e. ( 0 [,] +oo ) )

  proof
    cM
    cS
    cmeas
    cfv
    wcel
    cS
    cc0
    cpnf
    cicc
    co
    cA
    cM
    cS
    cM
    measfrge0
    ffvelrnda
end
