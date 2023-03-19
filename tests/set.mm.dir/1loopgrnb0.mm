include "cnbgr.mm"
include "co.mm"
include "cv.mm"
include "cpr.mm"
include "cedg.mm"
include "cfv.mm"
include "wcel.mm"
include "cvtx.mm"
include "csn.mm"
include "cdif.mm"
include "crab.mm"
include "c0.mm"
include "cupgr.mm"
include "wceq.mm"
include "cuspgr.mm"
include "1loopgruspgr.mm"
include "uspgrupgr.mm"
include "syl.mm"
include "eleq2d.mm"
include "mpbird.mm"
include "eqid.mm"
include "nbupgr.mm"
include "syl2anc.mm"
include "wn.mm"
include "wral.mm"
include "wa.mm"
include "difeq1d.mm"
include "wne.mm"
include "eldifsn.mm"
include "cvv.mm"
include "elexd.mm"
include "adantr.mm"
include "elex.mm"
include "adantl.mm"
include "preqsnd.mm"
include "simpr.mm"
include "syl6bi.mm"
include "necon3ad.mm"
include "expimpd.mm"
include "syl5bi.mm"
include "sylbid.mm"
include "imp.mm"
include "wb.mm"
include "1loopgredg.mm"
include "prex.mm"
include "elsn.mm"
include "syl6bb.mm"
include "notbid.mm"
include "ralrimiva.mm"
include "rabeq0.mm"
include "sylibr.mm"
include "eqtrd.mm"

theorem 1loopgrnb0
  let wph: wff ph
  let cA: class A
  let cG: class G
  let cN: class N
  let cV: class V
  let cX: class X
  let vv: setvar v
  assume 1loopgruspgr.v: |- ( ph -> ( Vtx ` G ) = V )
  assume 1loopgruspgr.a: |- ( ph -> A e. X )
  assume 1loopgruspgr.n: |- ( ph -> N e. V )
  assume 1loopgruspgr.i: |- ( ph -> ( iEdg ` G ) = { <. A , { N } >. } )


  assert |- ( ph -> ( G NeighbVtx N ) = (/) )

  proof
    wph
    cG
    cN
    cnbgr
    co
    #
    cN
    vv
    cv
    #
    cpr
    #
    cG
    cedg
    cfv
    #
    wcel
    #
    vv
    cG
    cvtx
    cfv
    #
    cN
    csn
    #
    cdif
    #
    crab
    #
    c0
    wph
    cG
    cupgr
    wcel
    #
    cN
    @5
    wcel
    #
    @0
    @8
    wceq
    wph
    cG
    cuspgr
    wcel
    @9
    wph
    cA
    cG
    cN
    cV
    cX
    1loopgruspgr.v
    1loopgruspgr.a
    1loopgruspgr.n
    1loopgruspgr.i
    1loopgruspgr
    cG
    uspgrupgr
    syl
    wph
    @10
    cN
    cV
    wcel
    1loopgruspgr.n
    wph
    @5
    cV
    cN
    1loopgruspgr.v
    eleq2d
    mpbird
    vv
    @3
    cG
    cN
    @5
    @5
    eqid
    @3
    eqid
    nbupgr
    syl2anc
    wph
    @4
    wn
    #
    vv
    @7
    wral
    @8
    c0
    wceq
    wph
    @11
    vv
    @7
    wph
    @1
    @7
    wcel
    #
    wa
    @11
    @2
    @6
    wceq
    #
    wn
    #
    wph
    @12
    @14
    wph
    @12
    @1
    cV
    @6
    cdif
    #
    wcel
    #
    @14
    wph
    @7
    @15
    @1
    wph
    @5
    cV
    @6
    1loopgruspgr.v
    difeq1d
    eleq2d
    @16
    @1
    cV
    wcel
    #
    @1
    cN
    wne
    #
    wa
    wph
    @14
    @1
    cV
    cN
    eldifsn
    wph
    @17
    @18
    @14
    wph
    @17
    wa
    #
    @13
    @1
    cN
    @19
    @13
    cN
    cN
    wceq
    #
    @1
    cN
    wceq
    #
    wa
    @21
    @19
    cN
    @1
    cN
    wph
    cN
    cvv
    wcel
    @17
    wph
    cN
    cV
    1loopgruspgr.n
    elexd
    adantr
    #
    @17
    @1
    cvv
    wcel
    wph
    @1
    cV
    elex
    adantl
    @22
    preqsnd
    @20
    @21
    simpr
    syl6bi
    necon3ad
    expimpd
    syl5bi
    sylbid
    imp
    wph
    @11
    @14
    wb
    @12
    wph
    @4
    @13
    wph
    @4
    @2
    @6
    csn
    #
    wcel
    @13
    wph
    @3
    @23
    @2
    wph
    cA
    cG
    cN
    cV
    cX
    1loopgruspgr.v
    1loopgruspgr.a
    1loopgruspgr.n
    1loopgruspgr.i
    1loopgredg
    eleq2d
    @2
    @6
    cN
    @1
    prex
    elsn
    syl6bb
    notbid
    adantr
    mpbird
    ralrimiva
    @4
    vv
    @7
    rabeq0
    sylibr
    eqtrd
end
