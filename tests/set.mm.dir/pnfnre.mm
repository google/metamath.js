include "cpnf.mm"
include "cr.mm"
include "wcel.mm"
include "cc.mm"
include "cuni.mm"
include "cpw.mm"
include "pwuninel.mm"
include "df-pnf.mm"
include "eleq1i.mm"
include "mtbir.mm"
include "recn.mm"
include "mto.mm"
include "nelir.mm"

theorem pnfnre



  assert |- +oo e/ RR

  proof
    cpnf
    cr
    cpnf
    cr
    wcel
    cpnf
    cc
    wcel
    #
    @0
    cc
    cuni
    cpw
    #
    cc
    wcel
    cc
    pwuninel
    cpnf
    @1
    cc
    df-pnf
    eleq1i
    mtbir
    cpnf
    recn
    mto
    nelir
end
