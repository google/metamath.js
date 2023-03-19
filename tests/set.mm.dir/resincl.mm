include "cr.mm"
include "wcel.mm"
include "csin.mm"
include "cfv.mm"
include "ci.mm"
include "cmul.mm"
include "co.mm"
include "ce.mm"
include "cim.mm"
include "resinval.mm"
include "cc.mm"
include "ax-icn.mm"
include "recn.mm"
include "mulcl.mm"
include "sylancr.mm"
include "efcl.mm"
include "syl.mm"
include "imcld.mm"
include "eqeltrd.mm"

theorem resincl
  let cA: class A


  assert |- ( A e. RR -> ( sin ` A ) e. RR )

  proof
    cA
    cr
    wcel
    #
    cA
    csin
    cfv
    ci
    cA
    cmul
    co
    #
    ce
    cfv
    #
    cim
    cfv
    cr
    cA
    resinval
    @0
    @2
    @0
    @1
    cc
    wcel
    #
    @2
    cc
    wcel
    @0
    ci
    cc
    wcel
    cA
    cc
    wcel
    @3
    ax-icn
    cA
    recn
    ci
    cA
    mulcl
    sylancr
    @1
    efcl
    syl
    imcld
    eqeltrd
end
