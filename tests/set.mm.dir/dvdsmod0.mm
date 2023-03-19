include "cz.mm"
include "wcel.mm"
include "wa.mm"
include "cn.mm"
include "cdvds.mm"
include "wbr.mm"
include "cmo.mm"
include "co.mm"
include "cc0.mm"
include "wceq.mm"
include "dvdszrcl.mm"
include "adantl.mm"
include "wi.mm"
include "dvdsval3.mm"
include "biimpd.mm"
include "expcom.mm"
include "impd.mm"
include "mpcom.mm"

theorem dvdsmod0
  let cM: class M
  let cN: class N


  assert |- ( ( M e. NN /\ M || N ) -> ( N mod M ) = 0 )

  proof
    cM
    cz
    wcel
    #
    cN
    cz
    wcel
    #
    wa
    #
    cM
    cn
    wcel
    #
    cM
    cN
    cdvds
    wbr
    #
    wa
    #
    cN
    cM
    cmo
    co
    cc0
    wceq
    #
    @4
    @2
    @3
    cM
    cN
    dvdszrcl
    adantl
    @1
    @5
    @6
    wi
    @0
    @1
    @3
    @4
    @6
    @3
    @1
    @4
    @6
    wi
    @3
    @1
    wa
    @4
    @6
    cM
    cN
    dvdsval3
    biimpd
    expcom
    impd
    adantl
    mpcom
end
