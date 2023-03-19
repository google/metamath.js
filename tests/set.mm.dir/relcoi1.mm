include "wrel.mm"
include "cid.mm"
include "cuni.mm"
include "cres.mm"
include "ccom.mm"
include "coires1.mm"
include "relresfld.mm"
include "syl5eq.mm"

theorem relcoi1
  let cR: class R


  assert |- ( Rel R -> ( R o. ( _I |` U. U. R ) ) = R )

  proof
    cR
    wrel
    cR
    cid
    cR
    cuni
    cuni
    #
    cres
    ccom
    cR
    @0
    cres
    cR
    cR
    @0
    coires1
    cR
    relresfld
    syl5eq
end
