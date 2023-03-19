include "cpnf.mm"
include "cxne.mm"
include "wceq.mm"
include "cmnf.mm"
include "cneg.mm"
include "cif.mm"
include "df-xneg.mm"
include "eqid.mm"
include "iftruei.mm"
include "eqtri.mm"

theorem xnegpnf



  assert |- -e +oo = -oo

  proof
    cpnf
    cxne
    cpnf
    cpnf
    wceq
    #
    cmnf
    cpnf
    cmnf
    wceq
    cpnf
    cpnf
    cneg
    cif
    #
    cif
    cmnf
    cpnf
    df-xneg
    @0
    cmnf
    @1
    cpnf
    eqid
    iftruei
    eqtri
end
