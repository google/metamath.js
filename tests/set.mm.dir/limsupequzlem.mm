include "ctp.mm"
include "cxr.mm"
include "clt.mm"
include "csup.mm"
include "cuz.mm"
include "cfv.mm"
include "cres.mm"
include "clsp.mm"
include "wceq.mm"
include "cv.mm"
include "wral.mm"
include "wcel.mm"
include "wa.mm"
include "eqid.mm"
include "cz.mm"
include "adantr.mm"
include "eluzelz.mm"
include "adantl.mm"
include "cr.mm"
include "zred.mm"
include "rexrd.mm"
include "zssxr.mm"
include "wss.mm"
include "tpssi.mm"
include "syl3anc.mm"
include "wor.mm"
include "cfn.mm"
include "c0.mm"
include "wne.mm"
include "xrltso.mm"
include "a1i.mm"
include "tpfi.mm"
include "tpnzd.mm"
include "sstrd.mm"
include "fisupcl.mm"
include "syl13anc.mm"
include "sseldd.mm"
include "sseldi.mm"
include "eluzelre.mm"
include "cle.mm"
include "wbr.mm"
include "tpid3g.mm"
include "syl.mm"
include "supxrubd.mm"
include "eluzle.mm"
include "xrletrd.mm"
include "eluzd.mm"
include "syldan.mm"
include "ralrimia.mm"
include "wfn.mm"
include "wb.mm"
include "tpid1g.mm"
include "uzss.mm"
include "tpid2g.mm"
include "fvreseq0.mm"
include "syl22anc.mm"
include "mpbird.mm"
include "fveq2d.mm"
include "cvv.mm"
include "fvexd.mm"
include "fnexd.mm"
include "cdm.mm"
include "fndmd.mm"
include "uzssz.mm"
include "syl6eqss.mm"
include "limsupresuz2.mm"
include "3eqtr3d.mm"

theorem limsupequzlem
  let wph: wff ph
  let vk: setvar k
  let cF: class F
  let cG: class G
  let cK: class K
  let cM: class M
  let cN: class N
  assume limsupequzlem.1: |- F/ k ph
  assume limsupequzlem.2: |- ( ph -> M e. ZZ )
  assume limsupequzlem.4: |- ( ph -> F Fn ( ZZ>= ` M ) )
  assume limsupequzlem.5: |- ( ph -> N e. ZZ )
  assume limsupequzlem.6: |- ( ph -> G Fn ( ZZ>= ` N ) )
  assume limsupequzlem.7: |- ( ph -> K e. ZZ )
  assume limsupequzlem.8: |- ( ( ph /\ k e. ( ZZ>= ` K ) ) -> ( F ` k ) = ( G ` k ) )

  disjoint F k
  disjoint G k
  disjoint K k
  disjoint M k
  disjoint N k
  assert |- ( ph -> ( limsup ` F ) = ( limsup ` G ) )

  proof
    wph
    cF
    cM
    cN
    cK
    ctp
    #
    cxr
    clt
    csup
    #
    cuz
    cfv
    #
    cres
    #
    clsp
    cfv
    cG
    @2
    cres
    #
    clsp
    cfv
    cF
    clsp
    cfv
    cG
    clsp
    cfv
    wph
    @3
    @4
    clsp
    wph
    @3
    @4
    wceq
    #
    vk
    cv
    #
    cF
    cfv
    @6
    cG
    cfv
    wceq
    #
    vk
    @2
    wral
    #
    wph
    @7
    vk
    @2
    limsupequzlem.1
    wph
    @6
    @2
    wcel
    #
    @6
    cK
    cuz
    cfv
    #
    wcel
    @7
    wph
    @9
    wa
    #
    cK
    @6
    @10
    @10
    eqid
    wph
    cK
    cz
    wcel
    #
    @9
    limsupequzlem.7
    adantr
    @9
    @6
    cz
    wcel
    wph
    @1
    @6
    eluzelz
    adantl
    @11
    cK
    @1
    @6
    @11
    cK
    wph
    cK
    cr
    wcel
    @9
    wph
    cK
    limsupequzlem.7
    zred
    adantr
    rexrd
    wph
    @1
    cxr
    wcel
    @9
    wph
    cz
    cxr
    @1
    zssxr
    wph
    @0
    cz
    @1
    wph
    cM
    cz
    wcel
    #
    cN
    cz
    wcel
    #
    @12
    @0
    cz
    wss
    limsupequzlem.2
    limsupequzlem.5
    limsupequzlem.7
    cM
    cN
    cK
    cz
    tpssi
    syl3anc
    #
    wph
    cxr
    clt
    wor
    #
    @0
    cfn
    wcel
    #
    @0
    c0
    wne
    @0
    cxr
    wss
    @1
    @0
    wcel
    @16
    wph
    xrltso
    a1i
    @17
    wph
    cM
    cN
    cK
    tpfi
    a1i
    wph
    cM
    cN
    cK
    cz
    limsupequzlem.2
    tpnzd
    wph
    @0
    cz
    cxr
    @15
    cz
    cxr
    wss
    wph
    zssxr
    a1i
    sstrd
    #
    cxr
    @0
    clt
    fisupcl
    syl13anc
    sseldd
    #
    sseldi
    adantr
    @11
    @6
    @9
    @6
    cr
    wcel
    wph
    @1
    @6
    eluzelre
    adantl
    rexrd
    wph
    cK
    @1
    cle
    wbr
    @9
    wph
    @0
    cK
    @1
    @18
    wph
    @12
    cK
    @0
    wcel
    limsupequzlem.7
    cK
    cz
    cM
    cN
    tpid3g
    syl
    @1
    eqid
    #
    supxrubd
    adantr
    @9
    @1
    @6
    cle
    wbr
    wph
    @1
    @6
    eluzle
    adantl
    xrletrd
    eluzd
    limsupequzlem.8
    syldan
    ralrimia
    wph
    cF
    cM
    cuz
    cfv
    #
    wfn
    cG
    cN
    cuz
    cfv
    #
    wfn
    @2
    @21
    wss
    #
    @2
    @22
    wss
    #
    @5
    @8
    wb
    limsupequzlem.4
    limsupequzlem.6
    wph
    @1
    @21
    wcel
    @23
    wph
    cM
    @1
    @21
    @21
    eqid
    limsupequzlem.2
    @19
    wph
    @0
    cM
    @1
    @18
    wph
    @13
    cM
    @0
    wcel
    limsupequzlem.2
    cM
    cz
    cN
    cK
    tpid1g
    syl
    @20
    supxrubd
    eluzd
    cM
    @1
    uzss
    syl
    wph
    @1
    @22
    wcel
    @24
    wph
    cN
    @1
    @22
    @22
    eqid
    limsupequzlem.5
    @19
    wph
    @0
    cN
    @1
    @18
    wph
    @14
    cN
    @0
    wcel
    limsupequzlem.5
    cN
    cz
    cM
    cK
    tpid2g
    syl
    @20
    supxrubd
    eluzd
    cN
    @1
    uzss
    syl
    vk
    @21
    @2
    @22
    cF
    cG
    fvreseq0
    syl22anc
    mpbird
    fveq2d
    wph
    cF
    @1
    cvv
    @2
    @19
    @2
    eqid
    #
    wph
    @21
    cF
    cvv
    limsupequzlem.4
    wph
    cM
    cuz
    fvexd
    fnexd
    wph
    cF
    cdm
    @21
    cz
    wph
    @21
    cF
    limsupequzlem.4
    fndmd
    cM
    uzssz
    syl6eqss
    limsupresuz2
    wph
    cG
    @1
    cvv
    @2
    @19
    @25
    wph
    @22
    cG
    cvv
    limsupequzlem.6
    wph
    cN
    cuz
    fvexd
    fnexd
    wph
    cG
    cdm
    @22
    cz
    wph
    @22
    cG
    limsupequzlem.6
    fndmd
    cN
    uzssz
    syl6eqss
    limsupresuz2
    3eqtr3d
end
