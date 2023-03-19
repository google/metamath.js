include "ccnfld.mm"
include "cmgp.mm"
include "cfv.mm"
include "cs2.mm"
include "ccxp.mm"
include "cof.mm"
include "co.mm"
include "cgsu.mm"
include "cmul.mm"
include "caddc.mm"
include "cle.mm"
include "cc0.mm"
include "c2.mm"
include "cfzo.mm"
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
include "ne0i.mm"
include "mp1i.mm"
include "chash.mm"
include "crp.mm"
include "wf.mm"
include "cword.mm"
include "s2cld.mm"
include "wrdf.mm"
include "syl.mm"
include "s2len.mm"
include "oveq2i.mm"
include "feq2i.mm"
include "sylib.mm"
include "c1.mm"
include "cmnd.mm"
include "cc.mm"
include "wceq.mm"
include "crg.mm"
include "cnring.mm"
include "ringmnd.mm"
include "rpcnd.mm"
include "cnfldbas.mm"
include "cnfldadd.mm"
include "gsumws2.mm"
include "syl3anc.mm"
include "eqtrd.mm"
include "amgmwlem.mm"
include "wa.mm"
include "jca.mm"
include "ofs2.mm"
include "syl2anc.mm"
include "oveq2d.mm"
include "ringmgp.mm"
include "rpred.mm"
include "rpcxpcld.mm"
include "mgpbas.mm"
include "cnfldmul.mm"
include "mgpplusg.mm"
include "rpmulcld.mm"
include "3brtr3d.mm"

theorem amgmw2d
  let wph: wff ph
  let cA: class A
  let cB: class B
  let cP: class P
  let cQ: class Q
  let vk: setvar k
  let vx: setvar x
  assume amgmw2d.0: |- ( ph -> A e. RR+ )
  assume amgmw2d.1: |- ( ph -> P e. RR+ )
  assume amgmw2d.2: |- ( ph -> B e. RR+ )
  assume amgmw2d.3: |- ( ph -> Q e. RR+ )
  assume amgmw2d.4: |- ( ph -> ( P + Q ) = 1 )


  assert |- ( ph -> ( ( A ^c P ) x. ( B ^c Q ) ) <_ ( ( A x. P ) + ( B x. Q ) ) )

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
    cP
    cQ
    cs2
    #
    ccxp
    cof
    co
    #
    cgsu
    co
    #
    ccnfld
    @1
    @2
    cmul
    cof
    co
    #
    cgsu
    co
    #
    cA
    cP
    ccxp
    co
    #
    cB
    cQ
    ccxp
    co
    #
    cmul
    co
    #
    cA
    cP
    cmul
    co
    #
    cB
    cQ
    cmul
    co
    #
    caddc
    co
    #
    cle
    wph
    cc0
    c2
    cfzo
    co
    #
    @1
    @0
    @2
    @0
    eqid
    #
    @13
    cfn
    wcel
    wph
    cc0
    c2
    fzofi
    a1i
    cc0
    @13
    wcel
    #
    @13
    c0
    wne
    wph
    @15
    c2
    cn
    wcel
    2nn
    c2
    lbfzo0
    mpbir
    @13
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
    @13
    crp
    @1
    wf
    wph
    @1
    crp
    cword
    #
    wcel
    @18
    wph
    cA
    cB
    crp
    amgmw2d.0
    amgmw2d.2
    s2cld
    crp
    @1
    wrdf
    syl
    @17
    @13
    crp
    @1
    @16
    c2
    cc0
    cfzo
    cA
    cB
    s2len
    oveq2i
    feq2i
    sylib
    wph
    cc0
    @2
    chash
    cfv
    #
    cfzo
    co
    #
    crp
    @2
    wf
    #
    @13
    crp
    @2
    wf
    wph
    @2
    @19
    wcel
    @22
    wph
    cP
    cQ
    crp
    amgmw2d.1
    amgmw2d.3
    s2cld
    crp
    @2
    wrdf
    syl
    @21
    @13
    crp
    @2
    @20
    c2
    cc0
    cfzo
    cP
    cQ
    s2len
    oveq2i
    feq2i
    sylib
    wph
    ccnfld
    @2
    cgsu
    co
    #
    cP
    cQ
    caddc
    co
    #
    c1
    wph
    ccnfld
    cmnd
    wcel
    #
    cP
    cc
    wcel
    cQ
    cc
    wcel
    @23
    @24
    wceq
    ccnfld
    crg
    wcel
    #
    @25
    wph
    cnring
    ccnfld
    ringmnd
    mp1i
    #
    wph
    cP
    amgmw2d.1
    rpcnd
    wph
    cQ
    amgmw2d.3
    rpcnd
    cc
    caddc
    cP
    cQ
    ccnfld
    cnfldbas
    cnfldadd
    gsumws2
    syl3anc
    amgmw2d.4
    eqtrd
    amgmwlem
    wph
    @4
    @0
    @7
    @8
    cs2
    #
    cgsu
    co
    #
    @9
    wph
    @3
    @28
    @0
    cgsu
    wph
    cA
    crp
    wcel
    #
    cB
    crp
    wcel
    #
    wa
    #
    cP
    crp
    wcel
    #
    cQ
    crp
    wcel
    #
    wa
    #
    @3
    @28
    wceq
    wph
    @30
    @31
    amgmw2d.0
    amgmw2d.2
    jca
    #
    wph
    @33
    @34
    amgmw2d.1
    amgmw2d.3
    jca
    #
    cA
    cB
    cP
    cQ
    ccxp
    crp
    crp
    ofs2
    syl2anc
    oveq2d
    wph
    @0
    cmnd
    wcel
    #
    @7
    cc
    wcel
    @8
    cc
    wcel
    @29
    @9
    wceq
    @26
    @38
    wph
    cnring
    ccnfld
    @0
    @14
    ringmgp
    mp1i
    wph
    @7
    wph
    cA
    cP
    amgmw2d.0
    wph
    cP
    amgmw2d.1
    rpred
    rpcxpcld
    rpcnd
    wph
    @8
    wph
    cB
    cQ
    amgmw2d.2
    wph
    cQ
    amgmw2d.3
    rpred
    rpcxpcld
    rpcnd
    cc
    cmul
    @7
    @8
    @0
    cc
    ccnfld
    @0
    @14
    cnfldbas
    mgpbas
    ccnfld
    cmul
    @0
    @14
    cnfldmul
    mgpplusg
    gsumws2
    syl3anc
    eqtrd
    wph
    @6
    ccnfld
    @10
    @11
    cs2
    #
    cgsu
    co
    #
    @12
    wph
    @5
    @39
    ccnfld
    cgsu
    wph
    @32
    @35
    @5
    @39
    wceq
    @36
    @37
    cA
    cB
    cP
    cQ
    cmul
    crp
    crp
    ofs2
    syl2anc
    oveq2d
    wph
    @25
    @10
    cc
    wcel
    @11
    cc
    wcel
    @40
    @12
    wceq
    @27
    wph
    @10
    wph
    cA
    cP
    amgmw2d.0
    amgmw2d.1
    rpmulcld
    rpcnd
    wph
    @11
    wph
    cB
    cQ
    amgmw2d.2
    amgmw2d.3
    rpmulcld
    rpcnd
    cc
    caddc
    @10
    @11
    ccnfld
    cnfldbas
    cnfldadd
    gsumws2
    syl3anc
    eqtrd
    3brtr3d
end
