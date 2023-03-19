include "c0.mm"
include "ccnv.mm"
include "wfun.mm"
include "fun0.mm"
include "cnv0.mm"
include "funeqi.mm"
include "mpbir.mm"

theorem funcnv0



  assert |- Fun `' (/)

  proof
    c0
    ccnv
    #
    wfun
    c0
    wfun
    fun0
    @0
    c0
    cnv0
    funeqi
    mpbir
end
