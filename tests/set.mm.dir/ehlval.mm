include "cn0.mm"
include "wcel.mm"
include "cehl.mm"
include "cfv.mm"
include "c1.mm"
include "cfz.mm"
include "co.mm"
include "crrx.mm"
include "cv.mm"
include "wceq.mm"
include "oveq2.mm"
include "fveq2d.mm"
include "df-ehl.mm"
include "fvex.mm"
include "fvmpt.mm"
include "syl5eq.mm"

theorem ehlval
  let cE: class E
  let cN: class N
  let vf: setvar f
  let vn: setvar n
  assume ehlval.e: |- E = ( EEhil ` N )


  assert |- ( N e. NN0 -> E = ( RR^ ` ( 1 ... N ) ) )

  proof
    cN
    cn0
    wcel
    cE
    cN
    cehl
    cfv
    c1
    cN
    cfz
    co
    #
    crrx
    cfv
    #
    ehlval.e
    vn
    cN
    c1
    vn
    cv
    #
    cfz
    co
    #
    crrx
    cfv
    @1
    cn0
    cehl
    @2
    cN
    wceq
    @3
    @0
    crrx
    @2
    cN
    c1
    cfz
    oveq2
    fveq2d
    vn
    df-ehl
    @0
    crrx
    fvex
    fvmpt
    syl5eq
end
