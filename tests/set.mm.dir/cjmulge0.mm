include "cc.mm"
include "wcel.mm"
include "cc0.mm"
include "cre.mm"
include "cfv.mm"
include "c2.mm"
include "cexp.mm"
include "co.mm"
include "cim.mm"
include "caddc.mm"
include "ccj.mm"
include "cmul.mm"
include "cle.mm"
include "recl.mm"
include "resqcld.mm"
include "imcl.mm"
include "sqge0d.mm"
include "addge0d.mm"
include "cjmulval.mm"
include "breqtrrd.mm"

theorem cjmulge0
  let cA: class A


  assert |- ( A e. CC -> 0 <_ ( A x. ( * ` A ) ) )

  proof
    cA
    cc
    wcel
    #
    cc0
    cA
    cre
    cfv
    #
    c2
    cexp
    co
    #
    cA
    cim
    cfv
    #
    c2
    cexp
    co
    #
    caddc
    co
    cA
    cA
    ccj
    cfv
    cmul
    co
    cle
    @0
    @2
    @4
    @0
    @1
    cA
    recl
    #
    resqcld
    @0
    @3
    cA
    imcl
    #
    resqcld
    @0
    @1
    @5
    sqge0d
    @0
    @3
    @6
    sqge0d
    addge0d
    cA
    cjmulval
    breqtrrd
end
