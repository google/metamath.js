include "cvv.mm"
include "wcel.mm"
include "wa.mm"
include "crngs.mm"
include "co.mm"
include "wf1o.mm"
include "rngimrcl.mm"
include "crngh.mm"
include "isrngim.mm"
include "simpr.mm"
include "syl6bi.mm"
include "mpcom.mm"

theorem rngimf1o
  let cB: class B
  let cC: class C
  let cR: class R
  let cS: class S
  let cF: class F
  let vk: setvar k
  let vx: setvar x
  assume rnghmf1o.b: |- B = ( Base ` R )
  assume rnghmf1o.c: |- C = ( Base ` S )


  assert |- ( F e. ( R RngIsom S ) -> F : B -1-1-onto-> C )

  proof
    cR
    cvv
    wcel
    cS
    cvv
    wcel
    wa
    #
    cF
    cR
    cS
    crngs
    co
    wcel
    #
    cB
    cC
    cF
    wf1o
    #
    cR
    cS
    cF
    rngimrcl
    @0
    @1
    cF
    cR
    cS
    crngh
    co
    wcel
    #
    @2
    wa
    @2
    cB
    cC
    cR
    cS
    cF
    cvv
    cvv
    rnghmf1o.b
    rnghmf1o.c
    isrngim
    @3
    @2
    simpr
    syl6bi
    mpcom
end
