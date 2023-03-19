include "cpi.mm"
include "cneg.mm"
include "cxr.mm"
include "wcel.mm"
include "cr.mm"
include "cioc.mm"
include "co.mm"
include "wss.mm"
include "pire.mm"
include "renegcli.mm"
include "rexri.mm"
include "iocssre.mm"
include "mp2an.mm"

theorem negpitopissre



  assert |- ( -u _pi (,] _pi ) C_ RR

  proof
    cpi
    cneg
    #
    cxr
    wcel
    cpi
    cr
    wcel
    @0
    cpi
    cioc
    co
    cr
    wss
    @0
    cpi
    pire
    renegcli
    rexri
    pire
    @0
    cpi
    iocssre
    mp2an
end
