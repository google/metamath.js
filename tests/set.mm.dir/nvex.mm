include "cop.mm"
include "cnv.mm"
include "wcel.mm"
include "cvv.mm"
include "wa.mm"
include "w3a.mm"
include "cvc.mm"
include "nvvcop.mm"
include "vcex.mm"
include "syl.mm"
include "cxp.mm"
include "nvss.mm"
include "sseli.mm"
include "opelxp2.mm"
include "df-3an.mm"
include "sylanbrc.mm"

theorem nvex
  let cS: class S
  let cG: class G
  let cN: class N


  assert |- ( <. <. G , S >. , N >. e. NrmCVec -> ( G e. _V /\ S e. _V /\ N e. _V ) )

  proof
    cG
    cS
    cop
    #
    cN
    cop
    #
    cnv
    wcel
    #
    cG
    cvv
    wcel
    #
    cS
    cvv
    wcel
    #
    wa
    #
    cN
    cvv
    wcel
    #
    @3
    @4
    @6
    w3a
    @2
    @0
    cvc
    wcel
    @5
    cN
    @0
    nvvcop
    cS
    cG
    vcex
    syl
    @2
    @1
    cvc
    cvv
    cxp
    #
    wcel
    @6
    cnv
    @7
    @1
    nvss
    sseli
    @0
    cN
    cvc
    cvv
    opelxp2
    syl
    @3
    @4
    @6
    df-3an
    sylanbrc
end
