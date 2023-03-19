include "cz.mm"
include "wcel.mm"
include "wa.mm"
include "cdvds.mm"
include "wbr.mm"
include "caddc.mm"
include "co.mm"
include "dvdsadd.mm"
include "cc.mm"
include "wceq.mm"
include "zcn.mm"
include "addcom.mm"
include "syl2an.mm"
include "breq2d.mm"
include "bitrd.mm"

theorem dvdsaddr
  let cM: class M
  let cN: class N


  assert |- ( ( M e. ZZ /\ N e. ZZ ) -> ( M || N <-> M || ( N + M ) ) )

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
    cN
    cdvds
    wbr
    cM
    cM
    cN
    caddc
    co
    #
    cdvds
    wbr
    cM
    cN
    cM
    caddc
    co
    #
    cdvds
    wbr
    cM
    cN
    dvdsadd
    @2
    @3
    @4
    cM
    cdvds
    @0
    cM
    cc
    wcel
    cN
    cc
    wcel
    @3
    @4
    wceq
    @1
    cM
    zcn
    cN
    zcn
    cM
    cN
    addcom
    syl2an
    breq2d
    bitrd
end
