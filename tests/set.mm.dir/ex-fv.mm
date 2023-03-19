include "c2.mm"
include "c6.mm"
include "cop.mm"
include "c3.mm"
include "c9.mm"
include "cpr.mm"
include "wceq.mm"
include "cfv.mm"
include "fveq1.mm"
include "wne.mm"
include "2re.mm"
include "2lt3.mm"
include "ltneii.mm"
include "3ex.mm"
include "cr.mm"
include "9re.mm"
include "elexi.mm"
include "fvpr2.mm"
include "ax-mp.mm"
include "syl6eq.mm"

theorem ex-fv
  let cF: class F


  assert |- ( F = { <. 2 , 6 >. , <. 3 , 9 >. } -> ( F ` 3 ) = 9 )

  proof
    cF
    c2
    c6
    cop
    c3
    c9
    cop
    cpr
    #
    wceq
    c3
    cF
    cfv
    c3
    @0
    cfv
    #
    c9
    c3
    cF
    @0
    fveq1
    c2
    c3
    wne
    @1
    c9
    wceq
    c2
    c3
    2re
    2lt3
    ltneii
    c2
    c3
    c6
    c9
    3ex
    c9
    cr
    9re
    elexi
    fvpr2
    ax-mp
    syl6eq
end
