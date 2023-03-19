include "com.mm"
include "word.mm"
include "wtr.mm"
include "wcel.mm"
include "wa.mm"
include "wi.mm"
include "ordom.mm"
include "ordtr.mm"
include "trel.mm"
include "mp2b.mm"

theorem elnn
  let cA: class A
  let cB: class B


  assert |- ( ( A e. B /\ B e. _om ) -> A e. _om )

  proof
    com
    word
    com
    wtr
    cA
    cB
    wcel
    cB
    com
    wcel
    wa
    cA
    com
    wcel
    wi
    ordom
    com
    ordtr
    com
    cA
    cB
    trel
    mp2b
end
