include "cr.mm"
include "wcel.mm"
include "ci.mm"
include "cmul.mm"
include "co.mm"
include "csin.mm"
include "cfv.mm"
include "cdiv.mm"
include "ce.mm"
include "cneg.mm"
include "cmin.mm"
include "c2.mm"
include "cc.mm"
include "wceq.mm"
include "recn.mm"
include "sinhval.mm"
include "syl.mm"
include "reefcl.mm"
include "renegcl.mm"
include "reefcld.mm"
include "resubcld.mm"
include "rehalfcld.mm"
include "eqeltrd.mm"

theorem resinhcl
  let cA: class A


  assert |- ( A e. RR -> ( ( sin ` ( _i x. A ) ) / _i ) e. RR )

  proof
    cA
    cr
    wcel
    #
    ci
    cA
    cmul
    co
    csin
    cfv
    ci
    cdiv
    co
    #
    cA
    ce
    cfv
    #
    cA
    cneg
    #
    ce
    cfv
    #
    cmin
    co
    #
    c2
    cdiv
    co
    #
    cr
    @0
    cA
    cc
    wcel
    @1
    @6
    wceq
    cA
    recn
    cA
    sinhval
    syl
    @0
    @5
    @0
    @2
    @4
    cA
    reefcl
    @0
    @3
    cA
    renegcl
    reefcld
    resubcld
    rehalfcld
    eqeltrd
end
