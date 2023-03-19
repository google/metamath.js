include "c2.mm"
include "cuz.mm"
include "cfv.mm"
include "wcel.mm"
include "c1.mm"
include "crmx.mm"
include "co.mm"
include "cexp.mm"
include "cmin.mm"
include "csqrt.mm"
include "crmy.mm"
include "cmul.mm"
include "caddc.mm"
include "wceq.mm"
include "wa.mm"
include "cz.mm"
include "1z.mm"
include "rmxyval.mm"
include "mpan2.mm"
include "rmbaserp.mm"
include "rpcnd.mm"
include "exp1d.mm"
include "rmspecpos.mm"
include "sqrtcld.mm"
include "mulid1d.mm"
include "eqcomd.mm"
include "oveq2d.mm"
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
include "eluzelz.mm"
include "zq.mm"
include "syl.mm"
include "sselii.mm"
include "a1i.mm"
include "qirropth.mm"
include "syl122anc.mm"
include "mpbid.mm"

theorem rmxy1
  let cA: class A


  assert |- ( A e. ( ZZ>= ` 2 ) -> ( ( A rmX 1 ) = A /\ ( A rmY 1 ) = 1 ) )

  proof
    cA
    c2
    cuz
    cfv
    #
    wcel
    #
    cA
    c1
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
    c1
    crmy
    co
    #
    cmul
    co
    caddc
    co
    #
    cA
    @4
    c1
    cmul
    co
    #
    caddc
    co
    #
    wceq
    #
    @2
    cA
    wceq
    @5
    c1
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
    c1
    cexp
    co
    #
    @11
    @8
    @1
    c1
    cz
    wcel
    #
    @6
    @12
    wceq
    1z
    cA
    c1
    rmxyval
    mpan2
    @1
    @11
    @1
    @11
    cA
    rmbaserp
    rpcnd
    exp1d
    @1
    @4
    @7
    cA
    caddc
    @1
    @7
    @4
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
    mulid1d
    eqcomd
    oveq2d
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
    cA
    cq
    wcel
    #
    c1
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
    1z
    cA
    c1
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
    1z
    cA
    c1
    cz
    @0
    cz
    crmy
    frmy
    fovcl
    mpan2
    sseldi
    @1
    cA
    cz
    wcel
    @14
    c2
    cA
    eluzelz
    cA
    zq
    syl
    @15
    @1
    cz
    cq
    c1
    zssq
    1z
    sselii
    a1i
    @4
    @2
    @5
    cA
    c1
    qirropth
    syl122anc
    mpbid
end
