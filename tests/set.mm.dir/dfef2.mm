include "cn.mm"
include "c1.mm"
include "cv.mm"
include "cdiv.mm"
include "co.mm"
include "caddc.mm"
include "cexp.mm"
include "cmpt.mm"
include "ce.mm"
include "cfv.mm"
include "cli.mm"
include "wbr.mm"
include "cc.mm"
include "wcel.mm"
include "crli.mm"
include "ccxp.mm"
include "wa.mm"
include "cn0.mm"
include "wceq.mm"
include "ax-1cn.mm"
include "simpl.mm"
include "nncn.mm"
include "adantl.mm"
include "cc0.mm"
include "wne.mm"
include "nnne0.mm"
include "divcld.mm"
include "addcl.mm"
include "sylancr.mm"
include "nnnn0.mm"
include "cxpexp.mm"
include "syl2anc.mm"
include "mpteq2dva.mm"
include "crp.mm"
include "wss.mm"
include "nnrp.mm"
include "ssriv.mm"
include "a1i.mm"
include "cabs.mm"
include "cmin.mm"
include "ccom.mm"
include "cbl.mm"
include "eqid.mm"
include "efrlim.mm"
include "rlimres2.mm"
include "eqbrtrrd.mm"
include "nnuz.mm"
include "1zzd.mm"
include "expcld.mm"
include "fmptd.mm"
include "rlimclim.mm"
include "mpbid.mm"
include "syl.mm"
include "cvv.mm"
include "nnex.mm"
include "mptex.mm"
include "oveq2.mm"
include "oveq2d.mm"
include "id.mm"
include "oveq12d.mm"
include "ovex.mm"
include "fvmpt.mm"
include "eqtr4d.mm"
include "climeq.mm"

theorem dfef2
  let wph: wff ph
  let cA: class A
  let vk: setvar k
  let cF: class F
  let cV: class V
  let vx: setvar x
  assume dfef2.1: |- ( ph -> F e. V )
  assume dfef2.2: |- ( ph -> A e. CC )
  assume dfef2.3: |- ( ( ph /\ k e. NN ) -> ( F ` k ) = ( ( 1 + ( A / k ) ) ^ k ) )

  disjoint A k
  disjoint F k
  disjoint k ph
  disjoint k x
  disjoint A x
  assert |- ( ph -> F ~~> ( exp ` A ) )

  proof
    wph
    vx
    cn
    c1
    cA
    vx
    cv
    #
    cdiv
    co
    #
    caddc
    co
    #
    @0
    cexp
    co
    #
    cmpt
    #
    cA
    ce
    cfv
    #
    cli
    wbr
    #
    cF
    @5
    cli
    wbr
    wph
    cA
    cc
    wcel
    #
    @6
    dfef2.2
    @7
    @4
    @5
    crli
    wbr
    @6
    @7
    vx
    cn
    @2
    @0
    ccxp
    co
    #
    cmpt
    @4
    @5
    crli
    @7
    vx
    cn
    @8
    @3
    @7
    @0
    cn
    wcel
    #
    wa
    #
    @2
    cc
    wcel
    #
    @0
    cn0
    wcel
    #
    @8
    @3
    wceq
    @10
    c1
    cc
    wcel
    @1
    cc
    wcel
    @11
    ax-1cn
    @10
    cA
    @0
    @7
    @9
    simpl
    @9
    @0
    cc
    wcel
    @7
    @0
    nncn
    adantl
    @9
    @0
    cc0
    wne
    @7
    @0
    nnne0
    adantl
    divcld
    c1
    @1
    addcl
    sylancr
    #
    @9
    @12
    @7
    @0
    nnnn0
    adantl
    #
    @2
    @0
    cxpexp
    syl2anc
    mpteq2dva
    @7
    vx
    cn
    crp
    @8
    @5
    cn
    crp
    wss
    @7
    vx
    cn
    crp
    @0
    nnrp
    ssriv
    a1i
    cA
    cc0
    c1
    cA
    cabs
    cfv
    c1
    caddc
    co
    cdiv
    co
    cabs
    cmin
    ccom
    cbl
    cfv
    co
    #
    vx
    @15
    eqid
    efrlim
    rlimres2
    eqbrtrrd
    @7
    @5
    @4
    c1
    cn
    nnuz
    @7
    1zzd
    @7
    vx
    cn
    @3
    cc
    @4
    @10
    @2
    @0
    @13
    @14
    expcld
    @4
    eqid
    #
    fmptd
    rlimclim
    mpbid
    syl
    wph
    @5
    vk
    @4
    cF
    c1
    cvv
    cV
    cn
    nnuz
    @4
    cvv
    wcel
    wph
    vx
    cn
    @3
    nnex
    mptex
    a1i
    dfef2.1
    wph
    1zzd
    wph
    vk
    cv
    #
    cn
    wcel
    #
    wa
    @17
    @4
    cfv
    #
    c1
    cA
    @17
    cdiv
    co
    #
    caddc
    co
    #
    @17
    cexp
    co
    #
    @17
    cF
    cfv
    @18
    @19
    @22
    wceq
    wph
    vx
    @17
    @3
    @22
    cn
    @4
    @0
    @17
    wceq
    #
    @2
    @21
    @0
    @17
    cexp
    @23
    @1
    @20
    c1
    caddc
    @0
    @17
    cA
    cdiv
    oveq2
    oveq2d
    @23
    id
    oveq12d
    @16
    @21
    @17
    cexp
    ovex
    fvmpt
    adantl
    dfef2.3
    eqtr4d
    climeq
    mpbid
end
