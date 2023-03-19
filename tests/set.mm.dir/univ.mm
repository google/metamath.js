include "cvv.mm"
include "cpw.mm"
include "cuni.mm"
include "pwv.mm"
include "unieqi.mm"
include "unipw.mm"
include "eqtr3i.mm"

theorem univ



  assert |- U. _V = _V

  proof
    cvv
    cpw
    #
    cuni
    cvv
    cuni
    cvv
    @0
    cvv
    pwv
    unieqi
    cvv
    unipw
    eqtr3i
end
