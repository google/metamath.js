include "crh.mm"
include "co.mm"
include "wcel.mm"
include "cmgp.mm"
include "cfv.mm"
include "c0g.mm"
include "cmhm.mm"
include "wceq.mm"
include "eqid.mm"
include "rhmmhm.mm"
include "mhm0.mm"
include "syl.mm"
include "ringidval.mm"
include "fveq2i.mm"
include "3eqtr4g.mm"

theorem rhm1
  let cR: class R
  let cS: class S
  let c.1: class .1.
  let cF: class F
  let cN: class N
  assume rhm1.o: |- .1. = ( 1r ` R )
  assume rhm1.n: |- N = ( 1r ` S )


  assert |- ( F e. ( R RingHom S ) -> ( F ` .1. ) = N )

  proof
    cF
    cR
    cS
    crh
    co
    wcel
    #
    cR
    cmgp
    cfv
    #
    c0g
    cfv
    #
    cF
    cfv
    #
    cS
    cmgp
    cfv
    #
    c0g
    cfv
    #
    c.1
    cF
    cfv
    cN
    @0
    cF
    @1
    @4
    cmhm
    co
    wcel
    @3
    @5
    wceq
    cR
    cS
    cF
    @1
    @4
    @1
    eqid
    #
    @4
    eqid
    #
    rhmmhm
    @1
    @4
    cF
    @5
    @2
    @2
    eqid
    @5
    eqid
    mhm0
    syl
    c.1
    @2
    cF
    cR
    c.1
    @1
    @6
    rhm1.o
    ringidval
    fveq2i
    cS
    cN
    @4
    @7
    rhm1.n
    ringidval
    3eqtr4g
end
