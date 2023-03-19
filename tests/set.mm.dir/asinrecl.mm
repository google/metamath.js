include "c1.mm"
include "cneg.mm"
include "cicc.mm"
include "co.mm"
include "wcel.mm"
include "cpi.mm"
include "c2.mm"
include "cdiv.mm"
include "cr.mm"
include "casin.mm"
include "cfv.mm"
include "wss.mm"
include "halfpire.mm"
include "renegcli.mm"
include "iccssre.mm"
include "mp2an.mm"
include "asinrebnd.mm"
include "sseldi.mm"

theorem asinrecl
  let cA: class A


  assert |- ( A e. ( -u 1 [,] 1 ) -> ( arcsin ` A ) e. RR )

  proof
    cA
    c1
    cneg
    c1
    cicc
    co
    wcel
    cpi
    c2
    cdiv
    co
    #
    cneg
    #
    @0
    cicc
    co
    #
    cr
    cA
    casin
    cfv
    @1
    cr
    wcel
    @0
    cr
    wcel
    @2
    cr
    wss
    @0
    halfpire
    renegcli
    halfpire
    @1
    @0
    iccssre
    mp2an
    cA
    asinrebnd
    sseldi
end
