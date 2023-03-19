include "ccnv.mm"
include "cc.mm"
include "cc0.mm"
include "csn.mm"
include "cdif.mm"
include "cima.mm"
include "cv.mm"
include "cfv.mm"
include "wf.mm"
include "wfun.mm"
include "wceq.mm"
include "ffun.mm"
include "difpreima.mm"
include "3syl.mm"
include "difss.mm"
include "syl6eqss.mm"
include "fimacnv.mm"
include "syl.mm"
include "sseqtrd.mm"
include "wcel.mm"
include "wa.mm"
include "wn.mm"
include "wo.mm"
include "cif.mm"
include "exmidd.mm"
include "wb.mm"
include "eqid.mm"
include "biantru.mm"
include "a1i.mm"
include "wne.mm"
include "crab.mm"
include "csupp.mm"
include "co.mm"
include "cvv.mm"
include "cn0.mm"
include "cuz.mm"
include "fvex.mm"
include "eqeltri.mm"
include "0nn0.mm"
include "ffs2.mm"
include "syl3anc.mm"
include "wfn.mm"
include "ffn.mm"
include "suppvalfn.mm"
include "eqtr3d.mm"
include "eleq2d.mm"
include "rabid.mm"
include "syl6bb.mm"
include "baibd.mm"
include "necon2bbid.mm"
include "biimprd.mm"
include "pm4.71d.mm"
include "orbi12d.mm"
include "mpbid.mm"
include "eqif.mm"
include "sylibr.mm"
include "sselda.mm"
include "ffvelrnda.mm"
include "syldan.mm"
include "fsumcvg3.mm"

theorem fsumcvg4
  let wph: wff ph
  let cS: class S
  let cF: class F
  let cM: class M
  let vk: setvar k
  assume fsumcvg4.s: |- S = ( ZZ>= ` M )
  assume fsumcvg4.m: |- ( ph -> M e. ZZ )
  assume fsumcvg4.c: |- ( ph -> F : S --> CC )
  assume fsumcvg4.f: |- ( ph -> ( `' F " ( CC \ { 0 } ) ) e. Fin )


  assert |- ( ph -> seq M ( + , F ) e. dom ~~> )

  proof
    wph
    cF
    ccnv
    #
    cc
    cc0
    csn
    #
    cdif
    #
    cima
    #
    vk
    cv
    #
    cF
    cfv
    #
    vk
    cF
    cM
    cS
    fsumcvg4.s
    fsumcvg4.m
    fsumcvg4.f
    wph
    @3
    @0
    cc
    cima
    #
    cS
    wph
    @3
    @6
    @0
    @1
    cima
    #
    cdif
    #
    @6
    wph
    cS
    cc
    cF
    wf
    #
    cF
    wfun
    @3
    @8
    wceq
    fsumcvg4.c
    cS
    cc
    cF
    ffun
    cc
    @1
    cF
    difpreima
    3syl
    @6
    @7
    difss
    syl6eqss
    wph
    @9
    @6
    cS
    wceq
    fsumcvg4.c
    cS
    cc
    cF
    fimacnv
    syl
    sseqtrd
    #
    wph
    @4
    cS
    wcel
    #
    wa
    #
    @4
    @3
    wcel
    #
    @5
    @5
    wceq
    #
    wa
    #
    @13
    wn
    #
    @5
    cc0
    wceq
    #
    wa
    #
    wo
    #
    @5
    @13
    @5
    cc0
    cif
    wceq
    @12
    @13
    @16
    wo
    @19
    @12
    @13
    exmidd
    @12
    @13
    @15
    @16
    @18
    @13
    @15
    wb
    @12
    @14
    @13
    @5
    eqid
    biantru
    a1i
    @12
    @16
    @17
    @12
    @17
    @16
    @12
    @13
    @5
    cc0
    wph
    @13
    @11
    @5
    cc0
    wne
    #
    wph
    @13
    @4
    @20
    vk
    cS
    crab
    #
    wcel
    @11
    @20
    wa
    wph
    @3
    @21
    @4
    wph
    cF
    cc0
    csupp
    co
    #
    @3
    @21
    wph
    cS
    cvv
    wcel
    #
    cc0
    cn0
    wcel
    #
    @9
    @22
    @3
    wceq
    @23
    wph
    cS
    cM
    cuz
    cfv
    cvv
    fsumcvg4.s
    cM
    cuz
    fvex
    eqeltri
    a1i
    #
    @24
    wph
    0nn0
    a1i
    #
    fsumcvg4.c
    cS
    cc
    @2
    cF
    cvv
    cn0
    cc0
    @2
    eqid
    ffs2
    syl3anc
    wph
    cF
    cS
    wfn
    #
    @23
    @24
    @22
    @21
    wceq
    wph
    @9
    @27
    fsumcvg4.c
    cS
    cc
    cF
    ffn
    syl
    @25
    @26
    vk
    cF
    cvv
    cn0
    cS
    cc0
    suppvalfn
    syl3anc
    eqtr3d
    eleq2d
    @20
    vk
    cS
    rabid
    syl6bb
    baibd
    necon2bbid
    biimprd
    pm4.71d
    orbi12d
    mpbid
    @13
    @5
    @5
    cc0
    eqif
    sylibr
    wph
    @13
    @11
    @5
    cc
    wcel
    wph
    @3
    cS
    @4
    @10
    sselda
    wph
    cS
    cc
    @4
    cF
    fsumcvg4.c
    ffvelrnda
    syldan
    fsumcvg3
end
