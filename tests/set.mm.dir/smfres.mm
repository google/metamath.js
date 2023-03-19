include "cdm.mm"
include "cin.mm"
include "cres.mm"
include "nfv.mm"
include "cuni.mm"
include "wss.mm"
include "inss1.mm"
include "a1i.mm"
include "eqid.mm"
include "smfdmss.mm"
include "sstrd.mm"
include "cr.mm"
include "wf.mm"
include "smff.mm"
include "fresin.mm"
include "syl.mm"
include "cv.mm"
include "wcel.mm"
include "wa.mm"
include "cfv.mm"
include "clt.mm"
include "wbr.mm"
include "crab.mm"
include "crest.mm"
include "co.mm"
include "ccnv.mm"
include "cmnf.mm"
include "cioo.mm"
include "cima.mm"
include "cvv.mm"
include "ovexd.mm"
include "adantr.mm"
include "csalg.mm"
include "csmblfn.mm"
include "cxr.mm"
include "mnfxr.mm"
include "rexr.mm"
include "adantl.mm"
include "smfpimioo.mm"
include "elrestd.mm"
include "wceq.mm"
include "wfun.mm"
include "ffund.mm"
include "respreima.mm"
include "eqcomd.mm"
include "preimaioomnf.mm"
include "eqtr2d.mm"
include "dmexd.mm"
include "restco.mm"
include "syl3anc.mm"
include "eleq12d.mm"
include "mpbird.mm"
include "issmfd.mm"

theorem smfres
  let wph: wff ph
  let cA: class A
  let cS: class S
  let cF: class F
  let cV: class V
  let va: setvar a
  let vx: setvar x
  let vk: setvar k
  assume smfres.s: |- ( ph -> S e. SAlg )
  assume smfres.f: |- ( ph -> F e. ( SMblFn ` S ) )
  assume smfres.a: |- ( ph -> A e. V )


  assert |- ( ph -> ( F |` A ) e. ( SMblFn ` S ) )

  proof
    wph
    vx
    cF
    cdm
    #
    cA
    cin
    #
    cS
    cF
    cA
    cres
    #
    va
    wph
    va
    nfv
    smfres.s
    wph
    @1
    @0
    cS
    cuni
    @1
    @0
    wss
    wph
    @0
    cA
    inss1
    a1i
    wph
    @0
    cS
    cF
    smfres.s
    smfres.f
    @0
    eqid
    #
    smfdmss
    sstrd
    wph
    @0
    cr
    cF
    wf
    @1
    cr
    @2
    wf
    #
    wph
    @0
    cS
    cF
    smfres.s
    smfres.f
    @3
    smff
    #
    @0
    cr
    cF
    cA
    fresin
    syl
    #
    wph
    va
    cv
    #
    cr
    wcel
    #
    wa
    #
    vx
    cv
    @2
    cfv
    @7
    clt
    wbr
    vx
    @1
    crab
    #
    cS
    @1
    crest
    co
    #
    wcel
    cF
    ccnv
    cmnf
    @7
    cioo
    co
    #
    cima
    #
    cA
    cin
    #
    cS
    @0
    crest
    co
    #
    cA
    crest
    co
    #
    wcel
    @9
    @14
    cA
    @15
    cvv
    cV
    @13
    @9
    cS
    @0
    crest
    ovexd
    wph
    cA
    cV
    wcel
    #
    @8
    smfres.a
    adantr
    @9
    cmnf
    @7
    @0
    cS
    cF
    wph
    cS
    csalg
    wcel
    #
    @8
    smfres.s
    adantr
    wph
    cF
    cS
    csmblfn
    cfv
    #
    wcel
    @8
    smfres.f
    adantr
    @3
    cmnf
    cxr
    wcel
    @9
    mnfxr
    a1i
    @8
    @7
    cxr
    wcel
    wph
    @7
    rexr
    adantl
    #
    smfpimioo
    @14
    eqid
    elrestd
    @9
    @10
    @14
    @11
    @16
    @9
    @14
    @2
    ccnv
    @12
    cima
    #
    @10
    wph
    @14
    @21
    wceq
    @8
    wph
    @21
    @14
    wph
    cF
    wfun
    @21
    @14
    wceq
    wph
    @0
    cr
    cF
    @5
    ffund
    @12
    cA
    cF
    respreima
    syl
    eqcomd
    adantr
    @9
    vx
    @1
    @7
    @2
    wph
    @4
    @8
    @6
    adantr
    @20
    preimaioomnf
    eqtr2d
    @9
    @16
    @11
    wph
    @16
    @11
    wceq
    #
    @8
    wph
    @18
    @0
    cvv
    wcel
    @17
    @22
    smfres.s
    wph
    cF
    @19
    smfres.f
    dmexd
    smfres.a
    @0
    cA
    cS
    csalg
    cvv
    cV
    restco
    syl3anc
    adantr
    eqcomd
    eleq12d
    mpbird
    issmfd
end
