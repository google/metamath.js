include "cn0.mm"
include "cz.mm"
include "cv.mm"
include "cc0.mm"
include "cfz.mm"
include "co.mm"
include "wcel.mm"
include "cfa.mm"
include "cfv.mm"
include "cmin.mm"
include "cmul.mm"
include "cdiv.mm"
include "cif.mm"
include "cbc.mm"
include "wceq.mm"
include "oveq2.mm"
include "eleq2d.mm"
include "fveq2.mm"
include "oveq1.mm"
include "fveq2d.mm"
include "oveq1d.mm"
include "oveq12d.mm"
include "ifbieq1d.mm"
include "eleq1.mm"
include "oveq2d.mm"
include "df-bc.mm"
include "ovex.mm"
include "c0ex.mm"
include "ifex.mm"
include "ovmpt2.mm"

theorem bcval
  let cK: class K
  let cN: class N
  let vk: setvar k
  let vn: setvar n


  assert |- ( ( N e. NN0 /\ K e. ZZ ) -> ( N _C K ) = if ( K e. ( 0 ... N ) , ( ( ! ` N ) / ( ( ! ` ( N - K ) ) x. ( ! ` K ) ) ) , 0 ) )

  proof
    vn
    vk
    cN
    cK
    cn0
    cz
    vk
    cv
    #
    cc0
    vn
    cv
    #
    cfz
    co
    #
    wcel
    #
    @1
    cfa
    cfv
    #
    @1
    @0
    cmin
    co
    #
    cfa
    cfv
    #
    @0
    cfa
    cfv
    #
    cmul
    co
    #
    cdiv
    co
    #
    cc0
    cif
    cK
    cc0
    cN
    cfz
    co
    #
    wcel
    #
    cN
    cfa
    cfv
    #
    cN
    cK
    cmin
    co
    #
    cfa
    cfv
    #
    cK
    cfa
    cfv
    #
    cmul
    co
    #
    cdiv
    co
    #
    cc0
    cif
    cbc
    @0
    @10
    wcel
    #
    @12
    cN
    @0
    cmin
    co
    #
    cfa
    cfv
    #
    @7
    cmul
    co
    #
    cdiv
    co
    #
    cc0
    cif
    @1
    cN
    wceq
    #
    @3
    @18
    @9
    @22
    cc0
    @23
    @2
    @10
    @0
    @1
    cN
    cc0
    cfz
    oveq2
    eleq2d
    @23
    @4
    @12
    @8
    @21
    cdiv
    @1
    cN
    cfa
    fveq2
    @23
    @6
    @20
    @7
    cmul
    @23
    @5
    @19
    cfa
    @1
    cN
    @0
    cmin
    oveq1
    fveq2d
    oveq1d
    oveq12d
    ifbieq1d
    @0
    cK
    wceq
    #
    @18
    @11
    @22
    @17
    cc0
    @0
    cK
    @10
    eleq1
    @24
    @21
    @16
    @12
    cdiv
    @24
    @20
    @14
    @7
    @15
    cmul
    @24
    @19
    @13
    cfa
    @0
    cK
    cN
    cmin
    oveq2
    fveq2d
    @0
    cK
    cfa
    fveq2
    oveq12d
    oveq2d
    ifbieq1d
    vk
    vn
    df-bc
    @11
    @17
    cc0
    @12
    @16
    cdiv
    ovex
    c0ex
    ifex
    ovmpt2
end
