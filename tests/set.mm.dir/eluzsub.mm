include "cz.mm"
include "wcel.mm"
include "caddc.mm"
include "co.mm"
include "cuz.mm"
include "cfv.mm"
include "cmin.mm"
include "wi.mm"
include "cc0.mm"
include "cif.mm"
include "wceq.mm"
include "oveq1.mm"
include "fveq2d.mm"
include "eleq2d.mm"
include "fveq2.mm"
include "imbi12d.mm"
include "oveq2.mm"
include "eleq1d.mm"
include "0z.mm"
include "elimel.mm"
include "eluzsubi.mm"
include "dedth2h.mm"
include "3impia.mm"

theorem eluzsub
  let cK: class K
  let cM: class M
  let cN: class N


  assert |- ( ( M e. ZZ /\ K e. ZZ /\ N e. ( ZZ>= ` ( M + K ) ) ) -> ( N - K ) e. ( ZZ>= ` M ) )

  proof
    cM
    cz
    wcel
    #
    cK
    cz
    wcel
    #
    cN
    cM
    cK
    caddc
    co
    #
    cuz
    cfv
    #
    wcel
    #
    cN
    cK
    cmin
    co
    #
    cM
    cuz
    cfv
    #
    wcel
    #
    @0
    @1
    @4
    @7
    wi
    cN
    @0
    cM
    cc0
    cif
    #
    cK
    caddc
    co
    #
    cuz
    cfv
    #
    wcel
    #
    @5
    @8
    cuz
    cfv
    #
    wcel
    #
    wi
    cN
    @8
    @1
    cK
    cc0
    cif
    #
    caddc
    co
    #
    cuz
    cfv
    #
    wcel
    #
    cN
    @14
    cmin
    co
    #
    @12
    wcel
    #
    wi
    cM
    cK
    cc0
    cc0
    cM
    @8
    wceq
    #
    @4
    @11
    @7
    @13
    @20
    @3
    @10
    cN
    @20
    @2
    @9
    cuz
    cM
    @8
    cK
    caddc
    oveq1
    fveq2d
    eleq2d
    @20
    @6
    @12
    @5
    cM
    @8
    cuz
    fveq2
    eleq2d
    imbi12d
    cK
    @14
    wceq
    #
    @11
    @17
    @13
    @19
    @21
    @10
    @16
    cN
    @21
    @9
    @15
    cuz
    cK
    @14
    @8
    caddc
    oveq2
    fveq2d
    eleq2d
    @21
    @5
    @18
    @12
    cK
    @14
    cN
    cmin
    oveq2
    eleq1d
    imbi12d
    @14
    @8
    cN
    cM
    cc0
    cz
    0z
    elimel
    cK
    cc0
    cz
    0z
    elimel
    eluzsubi
    dedth2h
    3impia
end
