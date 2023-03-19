include "cvv.mm"
include "wcel.mm"
include "wa.mm"
include "crs.mm"
include "co.mm"
include "crh.mm"
include "rimrcl.mm"
include "wf1o.mm"
include "isrim.mm"
include "simpl.mm"
include "syl6bi.mm"
include "mpcom.mm"

theorem rimrhm
  let cB: class B
  let cC: class C
  let cR: class R
  let cS: class S
  let cF: class F
  assume rhmf1o.b: |- B = ( Base ` R )
  assume rhmf1o.c: |- C = ( Base ` S )


  assert |- ( F e. ( R RingIso S ) -> F e. ( R RingHom S ) )

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
    cF
    cR
    cS
    crh
    co
    wcel
    #
    cR
    cS
    cF
    rimrcl
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
    rhmf1o.b
    rhmf1o.c
    isrim
    @2
    @3
    simpl
    syl6bi
    mpcom
end
