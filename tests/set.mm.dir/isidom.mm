include "ccrg.mm"
include "cdomn.mm"
include "cidom.mm"
include "df-idom.mm"
include "elin2.mm"

theorem isidom
  let cR: class R


  assert |- ( R e. IDomn <-> ( R e. CRing /\ R e. Domn ) )

  proof
    cR
    ccrg
    cdomn
    cidom
    df-idom
    elin2
end
