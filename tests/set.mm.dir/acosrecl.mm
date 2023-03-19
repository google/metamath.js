include "c1.mm"
include "cneg.mm"
include "cicc.mm"
include "co.mm"
include "wcel.mm"
include "cacos.mm"
include "cfv.mm"
include "cpi.mm"
include "c2.mm"
include "cdiv.mm"
include "casin.mm"
include "cmin.mm"
include "cr.mm"
include "cc.mm"
include "wceq.mm"
include "wss.mm"
include "neg1rr.mm"
include "1re.mm"
include "iccssre.mm"
include "mp2an.mm"
include "sseli.mm"
include "recnd.mm"
include "acosval.mm"
include "syl.mm"
include "halfpire.mm"
include "asinrecl.mm"
include "resubcl.mm"
include "sylancr.mm"
include "eqeltrd.mm"

theorem acosrecl
  let cA: class A


  assert |- ( A e. ( -u 1 [,] 1 ) -> ( arccos ` A ) e. RR )

  proof
    cA
    c1
    cneg
    #
    c1
    cicc
    co
    #
    wcel
    #
    cA
    cacos
    cfv
    #
    cpi
    c2
    cdiv
    co
    #
    cA
    casin
    cfv
    #
    cmin
    co
    #
    cr
    @2
    cA
    cc
    wcel
    @3
    @6
    wceq
    @2
    cA
    @1
    cr
    cA
    @0
    cr
    wcel
    c1
    cr
    wcel
    @1
    cr
    wss
    neg1rr
    1re
    @0
    c1
    iccssre
    mp2an
    sseli
    recnd
    cA
    acosval
    syl
    @2
    @4
    cr
    wcel
    @5
    cr
    wcel
    @6
    cr
    wcel
    halfpire
    cA
    asinrecl
    @4
    @5
    resubcl
    sylancr
    eqeltrd
end
