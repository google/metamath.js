include "cv.mm"
include "clt.mm"
include "wbr.mm"
include "cn0.mm"
include "cmpt.mm"
include "cfv.mm"
include "wceq.mm"
include "wi.mm"
include "wral.mm"
include "cgsu.mm"
include "co.mm"
include "cc0.mm"
include "cfz.mm"
include "csb.mm"
include "nfv.mm"
include "nfcsb1v.mm"
include "nfeq1.mm"
include "nfim.mm"
include "breq2.mm"
include "csbeq1a.mm"
include "eqeq1d.mm"
include "imbi12d.mm"
include "cbvral.mm"
include "sylib.mm"
include "wcel.mm"
include "wa.mm"
include "simpr.mm"
include "anim2i.mm"
include "ancoms.mm"
include "rspcsbela.mm"
include "syl.mm"
include "jca.mm"
include "adantr.mm"
include "eqid.mm"
include "fvmpts.mm"
include "eqtrd.mm"
include "ex.mm"
include "imim2d.mm"
include "ralimdva.mm"
include "mpd.mm"
include "cmap.mm"
include "wf.mm"
include "fmpt.mm"
include "cvv.mm"
include "wb.mm"
include "cbs.mm"
include "fvex.mm"
include "eqeltri.mm"
include "nn0ex.mm"
include "pm3.2i.mm"
include "elmapg.mm"
include "mp1i.mm"
include "mpbird.mm"
include "cres.mm"
include "wss.mm"
include "fz0ssnn0.mm"
include "resmpt.mm"
include "ax-mp.mm"
include "eqcomi.mm"
include "fsfnn0gsumfsffz.mm"

theorem gsummptnn0fz
  let wph: wff ph
  let cB: class B
  let cC: class C
  let cS: class S
  let vk: setvar k
  let cG: class G
  let c.0: class .0.
  let vx: setvar x
  assume gsummptnn0fz.k: |- F/ k ph
  assume gsummptnn0fz.b: |- B = ( Base ` G )
  assume gsummptnn0fz.0: |- .0. = ( 0g ` G )
  assume gsummptnn0fz.g: |- ( ph -> G e. CMnd )
  assume gsummptnn0fz.f: |- ( ph -> A. k e. NN0 C e. B )
  assume gsummptnn0fz.s: |- ( ph -> S e. NN0 )
  assume gsummptnn0fz.u: |- ( ph -> A. k e. NN0 ( S < k -> C = .0. ) )

  disjoint B k
  disjoint S k
  disjoint .0. k
  disjoint C x
  disjoint S x
  disjoint k x
  disjoint .0. x
  disjoint ph x
  assert |- ( ph -> ( G gsum ( k e. NN0 |-> C ) ) = ( G gsum ( k e. ( 0 ... S ) |-> C ) ) )

  proof
    wph
    cS
    vx
    cv
    #
    clt
    wbr
    #
    @0
    vk
    cn0
    cC
    cmpt
    #
    cfv
    #
    c.0
    wceq
    #
    wi
    #
    vx
    cn0
    wral
    #
    cG
    @2
    cgsu
    co
    cG
    vk
    cc0
    cS
    cfz
    co
    #
    cC
    cmpt
    #
    cgsu
    co
    wceq
    wph
    @1
    vk
    @0
    cC
    csb
    #
    c.0
    wceq
    #
    wi
    #
    vx
    cn0
    wral
    #
    @6
    wph
    cS
    vk
    cv
    #
    clt
    wbr
    #
    cC
    c.0
    wceq
    #
    wi
    #
    vk
    cn0
    wral
    @12
    gsummptnn0fz.u
    @16
    @11
    vk
    vx
    cn0
    @16
    vx
    nfv
    @1
    @10
    vk
    @1
    vk
    nfv
    vk
    @9
    c.0
    vk
    @0
    cC
    nfcsb1v
    nfeq1
    nfim
    @13
    @0
    wceq
    #
    @14
    @1
    @15
    @10
    @13
    @0
    cS
    clt
    breq2
    @17
    cC
    @9
    c.0
    vk
    @0
    cC
    csbeq1a
    eqeq1d
    imbi12d
    cbvral
    sylib
    wph
    @11
    @5
    vx
    cn0
    wph
    @0
    cn0
    wcel
    #
    wa
    #
    @10
    @4
    @1
    @19
    @10
    @4
    @19
    @10
    wa
    #
    @3
    @9
    c.0
    @20
    @18
    @9
    cB
    wcel
    #
    wa
    #
    @3
    @9
    wceq
    @19
    @22
    @10
    @19
    @18
    @21
    wph
    @18
    simpr
    @19
    @18
    cC
    cB
    wcel
    vk
    cn0
    wral
    #
    wa
    #
    @21
    @18
    wph
    @24
    wph
    @23
    @18
    gsummptnn0fz.f
    anim2i
    ancoms
    vk
    @0
    cn0
    cC
    cB
    rspcsbela
    syl
    jca
    adantr
    vk
    @0
    cC
    cn0
    @2
    cB
    @2
    eqid
    #
    fvmpts
    syl
    @19
    @10
    simpr
    eqtrd
    ex
    imim2d
    ralimdva
    mpd
    wph
    vx
    cB
    cS
    @2
    cG
    @8
    c.0
    gsummptnn0fz.b
    gsummptnn0fz.0
    gsummptnn0fz.g
    wph
    @2
    cB
    cn0
    cmap
    co
    wcel
    #
    cn0
    cB
    @2
    wf
    #
    wph
    @23
    @27
    gsummptnn0fz.f
    vk
    cn0
    cB
    cC
    @2
    @25
    fmpt
    sylib
    cB
    cvv
    wcel
    #
    cn0
    cvv
    wcel
    #
    wa
    @26
    @27
    wb
    wph
    @28
    @29
    cB
    cG
    cbs
    cfv
    cvv
    gsummptnn0fz.b
    cG
    cbs
    fvex
    eqeltri
    nn0ex
    pm3.2i
    cB
    cn0
    @2
    cvv
    cvv
    elmapg
    mp1i
    mpbird
    gsummptnn0fz.s
    @2
    @7
    cres
    #
    @8
    @7
    cn0
    wss
    @30
    @8
    wceq
    cS
    fz0ssnn0
    vk
    cn0
    @7
    cC
    resmpt
    ax-mp
    eqcomi
    fsfnn0gsumfsffz
    mpd
end
