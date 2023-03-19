include "cvv.mm"
include "wcel.mm"
include "wa.mm"
include "crs.mm"
include "co.mm"
include "wf1o.mm"
include "rimrcl.mm"
include "crh.mm"
include "isrim.mm"
include "simpr.mm"
include "syl6bi.mm"
include "mpcom.mm"

theorem rimf1o
  let cB: class B
  let cC: class C
  let cR: class R
  let cS: class S
  let cF: class F
  assume rhmf1o.b: |- B = ( Base ` R )
  assume rhmf1o.c: |- C = ( Base ` S )


  assert |- ( F e. ( R RingIso S ) -> F : B -1-1-onto-> C )

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
    crs
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
    rimrcl
    @0
    @1
    cF
    cR
    cS
    crh
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
    rhmf1o.b
    rhmf1o.c
    isrim
    @3
    @2
    simpr
    syl6bi
    mpcom
end
