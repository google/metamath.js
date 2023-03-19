include "cn.mm"
include "wcel.mm"
include "cee.mm"
include "cfv.mm"
include "cr.mm"
include "c1.mm"
include "cfz.mm"
include "co.mm"
include "cmap.mm"
include "wf.mm"
include "cv.mm"
include "wceq.mm"
include "oveq2.mm"
include "oveq2d.mm"
include "df-ee.mm"
include "ovex.mm"
include "fvmpt.mm"
include "eleq2d.mm"
include "reex.mm"
include "elmap.mm"
include "syl6bb.mm"

theorem elee
  let cA: class A
  let cN: class N
  let vn: setvar n


  assert |- ( N e. NN -> ( A e. ( EE ` N ) <-> A : ( 1 ... N ) --> RR ) )

  proof
    cN
    cn
    wcel
    #
    cA
    cN
    cee
    cfv
    #
    wcel
    cA
    cr
    c1
    cN
    cfz
    co
    #
    cmap
    co
    #
    wcel
    @2
    cr
    cA
    wf
    @0
    @1
    @3
    cA
    vn
    cN
    cr
    c1
    vn
    cv
    #
    cfz
    co
    #
    cmap
    co
    @3
    cn
    cee
    @4
    cN
    wceq
    @5
    @2
    cr
    cmap
    @4
    cN
    c1
    cfz
    oveq2
    oveq2d
    vn
    df-ee
    cr
    @2
    cmap
    ovex
    fvmpt
    eleq2d
    cr
    @2
    cA
    reex
    c1
    cN
    cfz
    ovex
    elmap
    syl6bb
end
