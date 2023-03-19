include "cc.mm"
include "wcel.mm"
include "csn.mm"
include "cxp.mm"
include "cdgr.mm"
include "cfv.mm"
include "cc0.mm"
include "cle.mm"
include "wbr.mm"
include "wceq.mm"
include "wss.mm"
include "cply.mm"
include "ssid.mm"
include "plyconst.mm"
include "mpan.mm"
include "cn0.mm"
include "0nn0.mm"
include "a1i.mm"
include "cv.mm"
include "cfz.mm"
include "co.mm"
include "simpl.mm"
include "cexp.mm"
include "cmul.mm"
include "csu.mm"
include "cmpt.mm"
include "wa.mm"
include "cz.mm"
include "0z.mm"
include "c1.mm"
include "exp0.mm"
include "oveq2d.mm"
include "mulid1.mm"
include "sylan9eqr.mm"
include "eqeltrd.mm"
include "oveq2.mm"
include "fsum1.mm"
include "sylancr.mm"
include "eqtrd.mm"
include "mpteq2dva.mm"
include "fconstmpt.mm"
include "syl6reqr.mm"
include "dgrle.mm"
include "wb.mm"
include "dgrcl.mm"
include "nn0le0eq0.mm"
include "3syl.mm"
include "mpbid.mm"

theorem 0dgr
  let cA: class A
  let vk: setvar k
  let vz: setvar z
  let cF: class F
  let cS: class S


  assert |- ( A e. CC -> ( deg ` ( CC X. { A } ) ) = 0 )

  proof
    cA
    cc
    wcel
    #
    cc
    cA
    csn
    cxp
    #
    cdgr
    cfv
    #
    cc0
    cle
    wbr
    #
    @2
    cc0
    wceq
    #
    @0
    vz
    cA
    cc
    vk
    @1
    cc0
    cc
    cc
    wss
    @0
    @1
    cc
    cply
    cfv
    wcel
    #
    cc
    ssid
    cA
    cc
    plyconst
    mpan
    #
    cc0
    cn0
    wcel
    @0
    0nn0
    a1i
    @0
    vk
    cv
    #
    cc0
    cc0
    cfz
    co
    #
    wcel
    simpl
    @0
    vz
    cc
    @8
    cA
    vz
    cv
    #
    @7
    cexp
    co
    #
    cmul
    co
    #
    vk
    csu
    #
    cmpt
    vz
    cc
    cA
    cmpt
    @1
    @0
    vz
    cc
    @12
    cA
    @0
    @9
    cc
    wcel
    #
    wa
    #
    @12
    cA
    @9
    cc0
    cexp
    co
    #
    cmul
    co
    #
    cA
    @14
    cc0
    cz
    wcel
    @16
    cc
    wcel
    @12
    @16
    wceq
    0z
    @14
    @16
    cA
    cc
    @13
    @0
    @16
    cA
    c1
    cmul
    co
    cA
    @13
    @15
    c1
    cA
    cmul
    @9
    exp0
    oveq2d
    cA
    mulid1
    sylan9eqr
    #
    @0
    @13
    simpl
    eqeltrd
    @11
    @16
    vk
    cc0
    @7
    cc0
    wceq
    @10
    @15
    cA
    cmul
    @7
    cc0
    @9
    cexp
    oveq2
    oveq2d
    fsum1
    sylancr
    @17
    eqtrd
    mpteq2dva
    vz
    cc
    cA
    fconstmpt
    syl6reqr
    dgrle
    @0
    @5
    @2
    cn0
    wcel
    @3
    @4
    wb
    @6
    cc
    @1
    dgrcl
    @2
    nn0le0eq0
    3syl
    mpbid
end
