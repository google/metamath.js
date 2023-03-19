include "cmnf.mm"
include "cr.mm"
include "wcel.mm"
include "cc.mm"
include "cuni.mm"
include "cpw.mm"
include "2pwuninel.mm"
include "cpnf.mm"
include "df-mnf.mm"
include "df-pnf.mm"
include "pweqi.mm"
include "eqtri.mm"
include "eleq1i.mm"
include "mtbir.mm"
include "recn.mm"
include "mto.mm"
include "nelir.mm"

theorem mnfnre



  assert |- -oo e/ RR

  proof
    cmnf
    cr
    cmnf
    cr
    wcel
    cmnf
    cc
    wcel
    #
    @0
    cc
    cuni
    cpw
    #
    cpw
    #
    cc
    wcel
    cc
    2pwuninel
    cmnf
    @2
    cc
    cmnf
    cpnf
    cpw
    @2
    df-mnf
    cpnf
    @1
    df-pnf
    pweqi
    eqtri
    eleq1i
    mtbir
    cmnf
    recn
    mto
    nelir
end
