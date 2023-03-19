include "cdr.mm"
include "ccrg.mm"
include "cfield.mm"
include "df-field.mm"
include "elin2.mm"

theorem isfld
  let cR: class R


  assert |- ( R e. Field <-> ( R e. DivRing /\ R e. CRing ) )

  proof
    cR
    cdr
    ccrg
    cfield
    df-field
    elin2
end
