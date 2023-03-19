include "ccnfld.mm"
include "cmgp.mm"
include "cfv.mm"
include "cs3.mm"
include "cgsu.mm"
include "co.mm"
include "c1.mm"
include "cc0.mm"
include "c3.mm"
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
include "3nn.mm"
include "lbfzo0.mm"
include "mpbir.mm"
include "ne0i.mm"
include "mp1i.mm"
include "crp.mm"
include "cword.mm"
include "wf.mm"
include "s3cld.mm"
include "c2.mm"
include "wrdf.mm"
include "s3len.mm"
include "df-3.mm"
include "eqtri.mm"
include "oveq2i.mm"
include "feq2i.mm"
include "sylib.mm"
include "sylibr.mm"
include "syl.mm"
include "amgmlem.mm"
include "cmnd.mm"
include "cc.mm"
include "wa.mm"
include "wceq.mm"
include "crg.mm"
include "cnring.mm"
include "ringmgp.mm"
include "rpcnd.mm"
include "jca32.mm"
include "cnfldbas.mm"
include "mgpbas.mm"
include "cnfldmul.mm"
include "mgpplusg.mm"
include "gsumws3.mm"
include "syl2anc.mm"
include "cn0.mm"
include "3nn0.mm"
include "hashfzo0.mm"
include "oveq2d.mm"
include "oveq12d.mm"
include "ringmnd.mm"
include "cnfldadd.mm"
include "3brtr3d.mm"

theorem amgm3d
  let wph: wff ph
  let cA: class A
  let cB: class B
  let cC: class C
  assume amgm3d.0: |- ( ph -> A e. RR+ )
  assume amgm3d.1: |- ( ph -> B e. RR+ )
  assume amgm3d.2: |- ( ph -> C e. RR+ )


  assert |- ( ph -> ( ( A x. ( B x. C ) ) ^c ( 1 / 3 ) ) <_ ( ( A + ( B + C ) ) / 3 ) )

  proof
    wph
    ccnfld
    cmgp
    cfv
    #
    cA
    cB
    cC
    cs3
    #
    cgsu
    co
    #
    c1
    cc0
    c3
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
    cmul
    co
    cmul
    co
    #
    c1
    c3
    cdiv
    co
    #
    ccxp
    co
    cA
    cB
    cC
    caddc
    co
    caddc
    co
    #
    c3
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
    c3
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
    c3
    cn
    wcel
    3nn
    c3
    lbfzo0
    mpbir
    @3
    cc0
    ne0i
    mp1i
    wph
    @1
    crp
    cword
    wcel
    #
    @3
    crp
    @1
    wf
    #
    wph
    cA
    cB
    cC
    crp
    amgm3d.0
    amgm3d.1
    amgm3d.2
    s3cld
    @12
    cc0
    c2
    c1
    caddc
    co
    #
    cfzo
    co
    #
    crp
    @1
    wf
    #
    @13
    @12
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
    @16
    crp
    @1
    wrdf
    @18
    @15
    crp
    @1
    @17
    @14
    cc0
    cfzo
    @17
    c3
    @14
    cA
    cB
    cC
    s3len
    df-3
    eqtri
    oveq2i
    feq2i
    sylib
    @3
    @15
    crp
    @1
    c3
    @14
    cc0
    cfzo
    df-3
    oveq2i
    feq2i
    sylibr
    syl
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
    @19
    wph
    cnring
    ccnfld
    @0
    @10
    ringmgp
    mp1i
    wph
    @20
    @21
    @22
    wph
    cA
    amgm3d.0
    rpcnd
    wph
    cB
    amgm3d.1
    rpcnd
    wph
    cC
    amgm3d.2
    rpcnd
    jca32
    #
    cc
    cmul
    cA
    cB
    cC
    @0
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
    gsumws3
    syl2anc
    wph
    @4
    c3
    c1
    cdiv
    c3
    cn0
    wcel
    @4
    c3
    wceq
    wph
    3nn0
    c3
    hashfzo0
    mp1i
    #
    oveq2d
    oveq12d
    wph
    @6
    @9
    @4
    c3
    cdiv
    wph
    ccnfld
    cmnd
    wcel
    #
    @23
    @6
    @9
    wceq
    @24
    @27
    wph
    cnring
    ccnfld
    ringmnd
    mp1i
    @25
    cc
    caddc
    cA
    cB
    cC
    ccnfld
    cnfldbas
    cnfldadd
    gsumws3
    syl2anc
    @26
    oveq12d
    3brtr3d
end
