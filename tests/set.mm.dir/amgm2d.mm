include "ccnfld.mm"
include "cmgp.mm"
include "cfv.mm"
include "cs2.mm"
include "cgsu.mm"
include "co.mm"
include "c1.mm"
include "cc0.mm"
include "c2.mm"
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
include "2nn.mm"
include "lbfzo0.mm"
include "mpbir.mm"
include "ne0ii.mm"
include "crp.mm"
include "cword.mm"
include "wf.mm"
include "s2cld.mm"
include "wrdf.mm"
include "s2len.mm"
include "eqcomi.mm"
include "oveq2i.mm"
include "feq2i.mm"
include "sylibr.mm"
include "syl.mm"
include "amgmlem.mm"
include "cmnd.mm"
include "cc.mm"
include "wceq.mm"
include "crg.mm"
include "cnring.mm"
include "ringmgp.mm"
include "mp1i.mm"
include "rpcnd.mm"
include "cnfldbas.mm"
include "mgpbas.mm"
include "cnfldmul.mm"
include "mgpplusg.mm"
include "gsumws2.mm"
include "syl3anc.mm"
include "cn0.mm"
include "2nn0.mm"
include "hashfzo0.mm"
include "oveq2d.mm"
include "oveq12d.mm"
include "ringmnd.mm"
include "cnfldadd.mm"
include "3brtr3d.mm"

theorem amgm2d
  let wph: wff ph
  let cA: class A
  let cB: class B
  assume amgm2d.0: |- ( ph -> A e. RR+ )
  assume amgm2d.1: |- ( ph -> B e. RR+ )


  assert |- ( ph -> ( ( A x. B ) ^c ( 1 / 2 ) ) <_ ( ( A + B ) / 2 ) )

  proof
    wph
    ccnfld
    cmgp
    cfv
    #
    cA
    cB
    cs2
    #
    cgsu
    co
    #
    c1
    cc0
    c2
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
    cmul
    co
    #
    c1
    c2
    cdiv
    co
    #
    ccxp
    co
    cA
    cB
    caddc
    co
    #
    c2
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
    c2
    fzofi
    a1i
    @3
    c0
    wne
    wph
    cc0
    @3
    cc0
    @3
    wcel
    c2
    cn
    wcel
    2nn
    c2
    lbfzo0
    mpbir
    ne0ii
    a1i
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
    crp
    amgm2d.0
    amgm2d.1
    s2cld
    @11
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
    @12
    crp
    @1
    wrdf
    @3
    @14
    crp
    @1
    c2
    @13
    cc0
    cfzo
    @13
    c2
    cA
    cB
    s2len
    eqcomi
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
    cA
    amgm2d.0
    rpcnd
    #
    wph
    cB
    amgm2d.1
    rpcnd
    #
    cc
    cmul
    cA
    cB
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
    gsumws2
    syl3anc
    wph
    @4
    c2
    c1
    cdiv
    c2
    cn0
    wcel
    @4
    c2
    wceq
    wph
    2nn0
    c2
    hashfzo0
    mp1i
    #
    oveq2d
    oveq12d
    wph
    @6
    @9
    @4
    c2
    cdiv
    wph
    ccnfld
    cmnd
    wcel
    #
    @16
    @17
    @6
    @9
    wceq
    @18
    @22
    wph
    cnring
    ccnfld
    ringmnd
    mp1i
    @19
    @20
    cc
    caddc
    cA
    cB
    ccnfld
    cnfldbas
    cnfldadd
    gsumws2
    syl3anc
    @21
    oveq12d
    3brtr3d
end
