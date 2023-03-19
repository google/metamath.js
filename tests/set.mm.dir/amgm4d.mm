include "ccnfld.mm"
include "cmgp.mm"
include "cfv.mm"
include "cs4.mm"
include "cgsu.mm"
include "co.mm"
include "c1.mm"
include "cc0.mm"
include "c4.mm"
include "cfzo.mm"
include "chash.mm"
include "cdiv.mm"
include "ccxp.mm"
include "cmul.mm"
include "caddc.mm"
include "cle.mm"
include "eqid.mm"
include "cfn.mm"
include "wcel.mm"
include "fzofi.mm"
include "a1i.mm"
include "c0.mm"
include "wne.mm"
include "cn.mm"
include "4nn.mm"
include "lbfzo0.mm"
include "mpbir.mm"
include "ne0i.mm"
include "mp1i.mm"
include "crp.mm"
include "wf.mm"
include "cword.mm"
include "s4cld.mm"
include "wrdf.mm"
include "syl.mm"
include "wceq.mm"
include "s4len.mm"
include "oveq2d.mm"
include "feq2d.mm"
include "mpbid.mm"
include "amgmlem.mm"
include "cmnd.mm"
include "cc.mm"
include "wa.mm"
include "crg.mm"
include "cnring.mm"
include "ringmgp.mm"
include "rpcnd.mm"
include "jca.mm"
include "jca32.mm"
include "cnfldbas.mm"
include "mgpbas.mm"
include "cnfldmul.mm"
include "mgpplusg.mm"
include "gsumws4.mm"
include "syl2anc.mm"
include "cn0.mm"
include "4nn0.mm"
include "hashfzo0.mm"
include "oveq12d.mm"
include "ringmnd.mm"
include "cnfldadd.mm"
include "3brtr3d.mm"

theorem amgm4d
  let wph: wff ph
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D
  assume amgm4d.0: |- ( ph -> A e. RR+ )
  assume amgm4d.1: |- ( ph -> B e. RR+ )
  assume amgm4d.2: |- ( ph -> C e. RR+ )
  assume amgm4d.3: |- ( ph -> D e. RR+ )


  assert |- ( ph -> ( ( A x. ( B x. ( C x. D ) ) ) ^c ( 1 / 4 ) ) <_ ( ( A + ( B + ( C + D ) ) ) / 4 ) )

  proof
    wph
    ccnfld
    cmgp
    cfv
    #
    cA
    cB
    cC
    cD
    cs4
    #
    cgsu
    co
    #
    c1
    cc0
    c4
    cfzo
    co
    #
    chash
    cfv
    #
    cdiv
    co
    #
    ccxp
    co
    ccnfld
    @1
    cgsu
    co
    #
    @4
    cdiv
    co
    cA
    cB
    cC
    cD
    cmul
    co
    cmul
    co
    cmul
    co
    #
    c1
    c4
    cdiv
    co
    #
    ccxp
    co
    cA
    cB
    cC
    cD
    caddc
    co
    caddc
    co
    caddc
    co
    #
    c4
    cdiv
    co
    cle
    wph
    @3
    @1
    @0
    @0
    eqid
    #
    @3
    cfn
    wcel
    wph
    cc0
    c4
    fzofi
    a1i
    cc0
    @3
    wcel
    #
    @3
    c0
    wne
    wph
    @11
    c4
    cn
    wcel
    4nn
    c4
    lbfzo0
    mpbir
    @3
    cc0
    ne0i
    mp1i
    wph
    cc0
    @1
    chash
    cfv
    #
    cfzo
    co
    #
    crp
    @1
    wf
    #
    @3
    crp
    @1
    wf
    wph
    @1
    crp
    cword
    wcel
    @14
    wph
    cA
    cB
    cC
    cD
    crp
    amgm4d.0
    amgm4d.1
    amgm4d.2
    amgm4d.3
    s4cld
    crp
    @1
    wrdf
    syl
    wph
    @13
    @3
    crp
    @1
    wph
    @12
    c4
    cc0
    cfzo
    @12
    c4
    wceq
    wph
    cA
    cB
    cC
    cD
    s4len
    a1i
    oveq2d
    feq2d
    mpbid
    amgmlem
    wph
    @2
    @7
    @5
    @8
    ccxp
    wph
    @0
    cmnd
    wcel
    #
    cA
    cc
    wcel
    #
    cB
    cc
    wcel
    #
    cC
    cc
    wcel
    #
    cD
    cc
    wcel
    #
    wa
    #
    wa
    wa
    #
    @2
    @7
    wceq
    ccnfld
    crg
    wcel
    #
    @15
    wph
    cnring
    ccnfld
    @0
    @10
    ringmgp
    mp1i
    wph
    @16
    @17
    @20
    wph
    cA
    amgm4d.0
    rpcnd
    wph
    cB
    amgm4d.1
    rpcnd
    wph
    @18
    @19
    wph
    cC
    amgm4d.2
    rpcnd
    wph
    cD
    amgm4d.3
    rpcnd
    jca
    jca32
    #
    cc
    cmul
    cA
    cB
    cC
    @0
    cD
    cc
    ccnfld
    @0
    @10
    cnfldbas
    mgpbas
    ccnfld
    cmul
    @0
    @10
    cnfldmul
    mgpplusg
    gsumws4
    syl2anc
    wph
    @4
    c4
    c1
    cdiv
    c4
    cn0
    wcel
    @4
    c4
    wceq
    wph
    4nn0
    c4
    hashfzo0
    mp1i
    #
    oveq2d
    oveq12d
    wph
    @6
    @9
    @4
    c4
    cdiv
    wph
    ccnfld
    cmnd
    wcel
    #
    @21
    @6
    @9
    wceq
    @22
    @25
    wph
    cnring
    ccnfld
    ringmnd
    mp1i
    @23
    cc
    caddc
    cA
    cB
    cC
    ccnfld
    cD
    cnfldbas
    cnfldadd
    gsumws4
    syl2anc
    @24
    oveq12d
    3brtr3d
end
