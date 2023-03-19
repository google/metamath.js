include "c2.mm"
include "cuz.mm"
include "cfv.mm"
include "wcel.mm"
include "cc0.mm"
include "crmx.mm"
include "co.mm"
include "cexp.mm"
include "c1.mm"
include "cmin.mm"
include "csqrt.mm"
include "crmy.mm"
include "cmul.mm"
include "caddc.mm"
include "wceq.mm"
include "wa.mm"
include "cz.mm"
include "0z.mm"
include "rmxyval.mm"
include "mpan2.mm"
include "rmbaserp.mm"
include "rpcnd.mm"
include "exp0d.mm"
include "rmspecpos.mm"
include "sqrtcld.mm"
include "mul01d.mm"
include "oveq2d.mm"
include "1p0e1.mm"
include "syl6req.mm"
include "3eqtrd.mm"
include "cc.mm"
include "cq.mm"
include "cdif.mm"
include "wb.mm"
include "rmspecsqrtnq.mm"
include "cn0.mm"
include "nn0ssq.mm"
include "frmx.mm"
include "fovcl.mm"
include "sseldi.mm"
include "zssq.mm"
include "frmy.mm"
include "1z.mm"
include "sselii.mm"
include "a1i.mm"
include "qirropth.mm"
include "syl122anc.mm"
include "mpbid.mm"

theorem rmxy0
  let cA: class A


  assert |- ( A e. ( ZZ>= ` 2 ) -> ( ( A rmX 0 ) = 1 /\ ( A rmY 0 ) = 0 ) )

  proof
    cA
    c2
    cuz
    cfv
    #
    wcel
    #
    cA
    cc0
    crmx
    co
    #
    cA
    c2
    cexp
    co
    c1
    cmin
    co
    #
    csqrt
    cfv
    #
    cA
    cc0
    crmy
    co
    #
    cmul
    co
    caddc
    co
    #
    c1
    @4
    cc0
    cmul
    co
    #
    caddc
    co
    #
    wceq
    #
    @2
    c1
    wceq
    @5
    cc0
    wceq
    wa
    #
    @1
    @6
    cA
    @4
    caddc
    co
    #
    cc0
    cexp
    co
    #
    c1
    @8
    @1
    cc0
    cz
    wcel
    #
    @6
    @12
    wceq
    0z
    cA
    cc0
    rmxyval
    mpan2
    @1
    @11
    @1
    @11
    cA
    rmbaserp
    rpcnd
    exp0d
    @1
    @8
    c1
    cc0
    caddc
    co
    c1
    @1
    @7
    cc0
    c1
    caddc
    @1
    @4
    @1
    @3
    @1
    @3
    cA
    rmspecpos
    rpcnd
    sqrtcld
    mul01d
    oveq2d
    1p0e1
    syl6req
    3eqtrd
    @1
    @4
    cc
    cq
    cdif
    wcel
    @2
    cq
    wcel
    @5
    cq
    wcel
    c1
    cq
    wcel
    #
    cc0
    cq
    wcel
    #
    @9
    @10
    wb
    cA
    rmspecsqrtnq
    @1
    cn0
    cq
    @2
    nn0ssq
    @1
    @13
    @2
    cn0
    wcel
    0z
    cA
    cc0
    cn0
    @0
    cz
    crmx
    frmx
    fovcl
    mpan2
    sseldi
    @1
    cz
    cq
    @5
    zssq
    @1
    @13
    @5
    cz
    wcel
    0z
    cA
    cc0
    cz
    @0
    cz
    crmy
    frmy
    fovcl
    mpan2
    sseldi
    @14
    @1
    cz
    cq
    c1
    zssq
    1z
    sselii
    a1i
    @15
    @1
    cz
    cq
    cc0
    zssq
    0z
    sselii
    a1i
    @4
    @2
    @5
    c1
    cc0
    qirropth
    syl122anc
    mpbid
end
