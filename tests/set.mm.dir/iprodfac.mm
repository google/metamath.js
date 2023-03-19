include "cn0.mm"
include "wcel.mm"
include "cn.mm"
include "c1.mm"
include "cv.mm"
include "cdiv.mm"
include "co.mm"
include "caddc.mm"
include "cexp.mm"
include "cprod.mm"
include "cfa.mm"
include "cfv.mm"
include "cmpt.mm"
include "nnuz.mm"
include "1zzd.mm"
include "facne0.mm"
include "eqid.mm"
include "faclim.mm"
include "wceq.mm"
include "weq.mm"
include "oveq2.mm"
include "oveq2d.mm"
include "oveq1d.mm"
include "oveq12d.mm"
include "ovex.mm"
include "fvmpt.mm"
include "adantl.mm"
include "wa.mm"
include "crp.mm"
include "1rp.mm"
include "a1i.mm"
include "simpr.mm"
include "nnrpd.mm"
include "rpreccld.mm"
include "rpaddcld.mm"
include "cz.mm"
include "nn0z.mm"
include "adantr.mm"
include "rpexpcld.mm"
include "1cnd.mm"
include "nn0nndivcl.mm"
include "recnd.mm"
include "addcomd.mm"
include "nn0ge0div.mm"
include "ge0p1rpd.mm"
include "eqeltrd.mm"
include "rpdivcld.mm"
include "rpcnd.mm"
include "iprodn0.mm"
include "eqcomd.mm"

theorem iprodfac
  let cA: class A
  let vk: setvar k
  let vx: setvar x

  disjoint A k
  disjoint A x
  disjoint k x
  assert |- ( A e. NN0 -> ( ! ` A ) = prod_ k e. NN ( ( ( 1 + ( 1 / k ) ) ^ A ) / ( 1 + ( A / k ) ) ) )

  proof
    cA
    cn0
    wcel
    #
    cn
    c1
    c1
    vk
    cv
    #
    cdiv
    co
    #
    caddc
    co
    #
    cA
    cexp
    co
    #
    c1
    cA
    @1
    cdiv
    co
    #
    caddc
    co
    #
    cdiv
    co
    #
    vk
    cprod
    cA
    cfa
    cfv
    #
    @0
    @7
    vk
    vx
    cn
    c1
    c1
    vx
    cv
    #
    cdiv
    co
    #
    caddc
    co
    #
    cA
    cexp
    co
    #
    c1
    cA
    @9
    cdiv
    co
    #
    caddc
    co
    #
    cdiv
    co
    #
    cmpt
    #
    c1
    @8
    cn
    nnuz
    @0
    1zzd
    cA
    facne0
    cA
    vx
    @16
    @16
    eqid
    #
    faclim
    @1
    cn
    wcel
    #
    @1
    @16
    cfv
    @7
    wceq
    @0
    vx
    @1
    @15
    @7
    cn
    @16
    vx
    vk
    weq
    #
    @12
    @4
    @14
    @6
    cdiv
    @19
    @11
    @3
    cA
    cexp
    @19
    @10
    @2
    c1
    caddc
    @9
    @1
    c1
    cdiv
    oveq2
    oveq2d
    oveq1d
    @19
    @13
    @5
    c1
    caddc
    @9
    @1
    cA
    cdiv
    oveq2
    oveq2d
    oveq12d
    @17
    @4
    @6
    cdiv
    ovex
    fvmpt
    adantl
    @0
    @18
    wa
    #
    @7
    @20
    @4
    @6
    @20
    @3
    cA
    @20
    c1
    @2
    c1
    crp
    wcel
    @20
    1rp
    a1i
    @20
    @1
    @20
    @1
    @0
    @18
    simpr
    nnrpd
    rpreccld
    rpaddcld
    @0
    cA
    cz
    wcel
    @18
    cA
    nn0z
    adantr
    rpexpcld
    @20
    @6
    @5
    c1
    caddc
    co
    crp
    @20
    c1
    @5
    @20
    1cnd
    @20
    @5
    cA
    @1
    nn0nndivcl
    #
    recnd
    addcomd
    @20
    @5
    @21
    cA
    @1
    nn0ge0div
    ge0p1rpd
    eqeltrd
    rpdivcld
    rpcnd
    iprodn0
    eqcomd
end
