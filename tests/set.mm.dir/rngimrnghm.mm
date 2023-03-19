include "cvv.mm"
include "wcel.mm"
include "wa.mm"
include "crngs.mm"
include "co.mm"
include "crngh.mm"
include "rngimrcl.mm"
include "wf1o.mm"
include "isrngim.mm"
include "simpl.mm"
include "syl6bi.mm"
include "mpcom.mm"

theorem rngimrnghm
  let cB: class B
  let cC: class C
  let cR: class R
  let cS: class S
  let cF: class F
  let vk: setvar k
  let vx: setvar x
  assume rnghmf1o.b: |- B = ( Base ` R )
  assume rnghmf1o.c: |- C = ( Base ` S )


  assert |- ( F e. ( R RngIsom S ) -> F e. ( R RngHomo S ) )

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
    cF
    cR
    cS
    crngh
    co
    wcel
    #
    cR
    cS
    cF
    rngimrcl
    @0
    @1
    @2
    cB
    cC
    cF
    wf1o
    #
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
    @2
    @3
    simpl
    syl6bi
    mpcom
end
