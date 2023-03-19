include "cuz.mm"
include "cfv.mm"
include "wcel.mm"
include "cz.mm"
include "caddc.mm"
include "co.mm"
include "eluzel2.mm"
include "wa.mm"
include "wi.mm"
include "cc0.mm"
include "cif.mm"
include "wceq.mm"
include "fveq2.mm"
include "eleq2d.mm"
include "oveq1.mm"
include "fveq2d.mm"
include "imbi12d.mm"
include "oveq2.mm"
include "eleq12d.mm"
include "imbi2d.mm"
include "0z.mm"
include "elimel.mm"
include "eluzaddi.mm"
include "dedth2h.mm"
include "com12.mm"
include "mpand.mm"
include "imp.mm"

theorem eluzadd
  let cK: class K
  let cM: class M
  let cN: class N


  assert |- ( ( N e. ( ZZ>= ` M ) /\ K e. ZZ ) -> ( N + K ) e. ( ZZ>= ` ( M + K ) ) )

  proof
    cN
    cM
    cuz
    cfv
    #
    wcel
    #
    cK
    cz
    wcel
    #
    cN
    cK
    caddc
    co
    #
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
    @1
    cM
    cz
    wcel
    #
    @2
    @6
    cM
    cN
    eluzel2
    @7
    @2
    wa
    @1
    @6
    @7
    @2
    @1
    @6
    wi
    cN
    @7
    cM
    cc0
    cif
    #
    cuz
    cfv
    #
    wcel
    #
    @3
    @8
    cK
    caddc
    co
    #
    cuz
    cfv
    #
    wcel
    #
    wi
    @10
    cN
    @2
    cK
    cc0
    cif
    #
    caddc
    co
    #
    @8
    @14
    caddc
    co
    #
    cuz
    cfv
    #
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
    @1
    @10
    @6
    @13
    @19
    @0
    @9
    cN
    cM
    @8
    cuz
    fveq2
    eleq2d
    @19
    @5
    @12
    @3
    @19
    @4
    @11
    cuz
    cM
    @8
    cK
    caddc
    oveq1
    fveq2d
    eleq2d
    imbi12d
    cK
    @14
    wceq
    #
    @13
    @18
    @10
    @20
    @3
    @15
    @12
    @17
    cK
    @14
    cN
    caddc
    oveq2
    @20
    @11
    @16
    cuz
    cK
    @14
    @8
    caddc
    oveq2
    fveq2d
    eleq12d
    imbi2d
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
    eluzaddi
    dedth2h
    com12
    mpand
    imp
end
