include "cdm.mm"
include "nfv.mm"
include "cvol.mm"
include "csalg.mm"
include "wceq.mm"
include "a1i.mm"
include "wcel.mm"
include "dmvolsal.mm"
include "eqeltrd.mm"
include "cr.mm"
include "cuni.mm"
include "cmbf.mm"
include "wss.mm"
include "mbfdmssre.mm"
include "syl.mm"
include "unieqi.mm"
include "unidmvol.mm"
include "eqtri.mm"
include "syl6sseqr.mm"
include "wfn.mm"
include "crn.mm"
include "wa.mm"
include "wf.mm"
include "cc.mm"
include "mbff.mm"
include "ffn.mm"
include "3syl.mm"
include "jca.mm"
include "df-f.mm"
include "sylibr.mm"
include "cv.mm"
include "cfv.mm"
include "clt.mm"
include "wbr.mm"
include "crab.mm"
include "ccnv.mm"
include "cmnf.mm"
include "cioo.mm"
include "co.mm"
include "cima.mm"
include "crest.mm"
include "adantr.mm"
include "cxr.mm"
include "rexr.mm"
include "adantl.mm"
include "preimaioomnf.mm"
include "eqcomd.mm"
include "cvv.mm"
include "elexi.mm"
include "eqeltri.mm"
include "dmexd.mm"
include "mbfima.mm"
include "syl2anc.mm"
include "eleqtrrd.mm"
include "cin.mm"
include "cnvimass.mm"
include "dfss.mm"
include "biimpi.mm"
include "ax-mp.mm"
include "elrestd.mm"
include "issmfd.mm"

theorem mbfresmf
  let wph: wff ph
  let cS: class S
  let cF: class F
  let va: setvar a
  let vx: setvar x
  let vk: setvar k
  assume mbfresmf.1: |- ( ph -> F e. MblFn )
  assume mbfresmf.2: |- ( ph -> ran F C_ RR )
  assume mbfresmf.3: |- S = dom vol


  assert |- ( ph -> F e. ( SMblFn ` S ) )

  proof
    wph
    vx
    cF
    cdm
    #
    cS
    cF
    va
    wph
    va
    nfv
    wph
    cS
    cvol
    cdm
    #
    csalg
    cS
    @1
    wceq
    wph
    mbfresmf.3
    a1i
    #
    @1
    csalg
    wcel
    wph
    dmvolsal
    a1i
    eqeltrd
    wph
    @0
    cr
    cS
    cuni
    #
    wph
    cF
    cmbf
    wcel
    #
    @0
    cr
    wss
    mbfresmf.1
    cF
    mbfdmssre
    syl
    @3
    @1
    cuni
    cr
    cS
    @1
    mbfresmf.3
    unieqi
    unidmvol
    eqtri
    syl6sseqr
    wph
    cF
    @0
    wfn
    #
    cF
    crn
    cr
    wss
    #
    wa
    @0
    cr
    cF
    wf
    #
    wph
    @5
    @6
    wph
    @4
    @0
    cc
    cF
    wf
    @5
    mbfresmf.1
    cF
    mbff
    @0
    cc
    cF
    ffn
    3syl
    mbfresmf.2
    jca
    @0
    cr
    cF
    df-f
    sylibr
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
    cF
    cfv
    @9
    clt
    wbr
    vx
    @0
    crab
    #
    cF
    ccnv
    cmnf
    @9
    cioo
    co
    #
    cima
    #
    cS
    @0
    crest
    co
    @11
    @14
    @12
    @11
    vx
    @0
    @9
    cF
    wph
    @7
    @10
    @8
    adantr
    @10
    @9
    cxr
    wcel
    wph
    @9
    rexr
    adantl
    preimaioomnf
    eqcomd
    @11
    @14
    @0
    cS
    cvv
    cvv
    @14
    cS
    cvv
    wcel
    @11
    cS
    @1
    cvv
    mbfresmf.3
    @1
    csalg
    dmvolsal
    elexi
    eqeltri
    a1i
    wph
    @0
    cvv
    wcel
    @10
    wph
    cF
    cmbf
    mbfresmf.1
    dmexd
    adantr
    wph
    @14
    cS
    wcel
    @10
    wph
    @14
    @1
    cS
    wph
    @4
    @7
    @14
    @1
    wcel
    mbfresmf.1
    @8
    @0
    cmnf
    @9
    cF
    mbfima
    syl2anc
    @2
    eleqtrrd
    adantr
    @14
    @0
    wss
    #
    @14
    @14
    @0
    cin
    wceq
    #
    cF
    @13
    cnvimass
    @15
    @16
    @14
    @0
    dfss
    biimpi
    ax-mp
    elrestd
    eqeltrd
    issmfd
end
