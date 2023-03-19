include "cn0.mm"
include "wcel.mm"
include "cn.mm"
include "wa.mm"
include "c1.mm"
include "cdiv.mm"
include "co.mm"
include "caddc.mm"
include "cexp.mm"
include "cmul.mm"
include "crp.mm"
include "1rp.mm"
include "a1i.mm"
include "nnrp.mm"
include "rpreccld.mm"
include "adantl.mm"
include "rpaddcld.mm"
include "rpcnd.mm"
include "simpl.mm"
include "expp1d.mm"
include "cz.mm"
include "nn0z.mm"
include "rpexpcl.mm"
include "syl2anr.mm"
include "1cnd.mm"
include "nn0nndivcl.mm"
include "recnd.mm"
include "addcomd.mm"
include "nn0ge0div.mm"
include "ge0p1rpd.mm"
include "eqeltrd.mm"
include "rpne0d.mm"
include "divcan1d.mm"
include "oveq1d.mm"
include "rpdivcld.mm"
include "mulassd.mm"
include "3eqtr2d.mm"
include "rpmulcld.mm"
include "nn0p1nn.mm"
include "nnrpd.mm"
include "adantr.mm"
include "divassd.mm"
include "eqtrd.mm"

theorem faclimlem3
  let cB: class B
  let cM: class M


  assert |- ( ( M e. NN0 /\ B e. NN ) -> ( ( ( 1 + ( 1 / B ) ) ^ ( M + 1 ) ) / ( 1 + ( ( M + 1 ) / B ) ) ) = ( ( ( ( 1 + ( 1 / B ) ) ^ M ) / ( 1 + ( M / B ) ) ) x. ( ( ( 1 + ( M / B ) ) x. ( 1 + ( 1 / B ) ) ) / ( 1 + ( ( M + 1 ) / B ) ) ) ) )

  proof
    cM
    cn0
    wcel
    #
    cB
    cn
    wcel
    #
    wa
    #
    c1
    c1
    cB
    cdiv
    co
    #
    caddc
    co
    #
    cM
    c1
    caddc
    co
    #
    cexp
    co
    #
    c1
    @5
    cB
    cdiv
    co
    #
    caddc
    co
    #
    cdiv
    co
    @4
    cM
    cexp
    co
    #
    c1
    cM
    cB
    cdiv
    co
    #
    caddc
    co
    #
    cdiv
    co
    #
    @11
    @4
    cmul
    co
    #
    cmul
    co
    #
    @8
    cdiv
    co
    @12
    @13
    @8
    cdiv
    co
    cmul
    co
    @2
    @6
    @14
    @8
    cdiv
    @2
    @6
    @9
    @4
    cmul
    co
    @12
    @11
    cmul
    co
    #
    @4
    cmul
    co
    @14
    @2
    @4
    cM
    @2
    @4
    @2
    c1
    @3
    c1
    crp
    wcel
    #
    @2
    1rp
    a1i
    #
    @1
    @3
    crp
    wcel
    @0
    @1
    cB
    cB
    nnrp
    #
    rpreccld
    #
    adantl
    rpaddcld
    #
    rpcnd
    #
    @0
    @1
    simpl
    expp1d
    @2
    @15
    @9
    @4
    cmul
    @2
    @9
    @11
    @2
    @9
    @1
    @4
    crp
    wcel
    cM
    cz
    wcel
    @9
    crp
    wcel
    @0
    @1
    c1
    @3
    @16
    @1
    1rp
    a1i
    @19
    rpaddcld
    cM
    nn0z
    @4
    cM
    rpexpcl
    syl2anr
    #
    rpcnd
    @2
    @11
    @2
    @11
    @10
    c1
    caddc
    co
    crp
    @2
    c1
    @10
    @2
    1cnd
    @2
    @10
    cM
    cB
    nn0nndivcl
    #
    recnd
    addcomd
    @2
    @10
    @23
    cM
    cB
    nn0ge0div
    ge0p1rpd
    eqeltrd
    #
    rpcnd
    #
    @2
    @11
    @24
    rpne0d
    divcan1d
    oveq1d
    @2
    @12
    @11
    @4
    @2
    @12
    @2
    @9
    @11
    @22
    @24
    rpdivcld
    rpcnd
    #
    @25
    @21
    mulassd
    3eqtr2d
    oveq1d
    @2
    @12
    @13
    @8
    @26
    @2
    @13
    @2
    @11
    @4
    @24
    @20
    rpmulcld
    rpcnd
    @2
    @8
    @2
    c1
    @7
    @17
    @2
    @5
    cB
    @0
    @5
    crp
    wcel
    @1
    @0
    @5
    cM
    nn0p1nn
    nnrpd
    adantr
    @1
    cB
    crp
    wcel
    @0
    @18
    adantl
    rpdivcld
    rpaddcld
    #
    rpcnd
    @2
    @8
    @27
    rpne0d
    divassd
    eqtrd
end
