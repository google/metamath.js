include "cv.mm"
include "cfv.mm"
include "csn.mm"
include "cnei.mm"
include "crest.mm"
include "co.mm"
include "cflf.mm"
include "wcel.mm"
include "cflim.mm"
include "wral.mm"
include "cfil.mm"
include "wf.mm"
include "ccn.mm"
include "wa.mm"
include "ctopon.mm"
include "wb.mm"
include "wss.mm"
include "ctop.mm"
include "toptopon.mm"
include "sylib.mm"
include "resttopon.mm"
include "syl2anc.mm"
include "cntop2.mm"
include "syl.mm"
include "cnflf.mm"
include "mpbid.mm"
include "simprd.mm"
include "ccl.mm"
include "sscls.mm"
include "sseldd.mm"
include "trnei.mm"
include "syl3anc.mm"
include "wceq.mm"
include "oveq2.mm"
include "fveq1d.mm"
include "eleq2d.mm"
include "raleqbidv.mm"
include "adantl.mm"
include "rspcdv.mm"
include "mpd.mm"
include "neiflim.mm"
include "snssd.mm"
include "neitr.mm"
include "oveq2d.mm"
include "eleqtrd.mm"
include "fveq2.mm"
include "eleq1d.mm"

theorem flfcntr
  let wph: wff ph
  let cA: class A
  let cB: class B
  let cC: class C
  let cF: class F
  let cJ: class J
  let cK: class K
  let cX: class X
  let va: setvar a
  let vx: setvar x
  assume flfcntr.c: |- C = U. J
  assume flfcntr.b: |- B = U. K
  assume flfcntr.j: |- ( ph -> J e. Top )
  assume flfcntr.a: |- ( ph -> A C_ C )
  assume flfcntr.1: |- ( ph -> F e. ( ( J |`t A ) Cn K ) )
  assume flfcntr.y: |- ( ph -> X e. A )


  assert |- ( ph -> ( F ` X ) e. ( ( K fLimf ( ( ( nei ` J ) ` { X } ) |`t A ) ) ` F ) )

  proof
    wph
    vx
    cv
    #
    cF
    cfv
    #
    cF
    cK
    cX
    csn
    #
    cJ
    cnei
    cfv
    cfv
    cA
    crest
    co
    #
    cflf
    co
    #
    cfv
    #
    wcel
    #
    vx
    cJ
    cA
    crest
    co
    #
    @3
    cflim
    co
    #
    wral
    #
    cX
    cF
    cfv
    #
    @5
    wcel
    #
    wph
    @1
    cF
    cK
    va
    cv
    #
    cflf
    co
    #
    cfv
    #
    wcel
    #
    vx
    @7
    @12
    cflim
    co
    #
    wral
    #
    va
    cA
    cfil
    cfv
    #
    wral
    #
    @9
    wph
    cA
    cB
    cF
    wf
    #
    @19
    wph
    cF
    @7
    cK
    ccn
    co
    wcel
    #
    @20
    @19
    wa
    #
    flfcntr.1
    wph
    @7
    cA
    ctopon
    cfv
    wcel
    #
    cK
    cB
    ctopon
    cfv
    wcel
    #
    @21
    @22
    wb
    wph
    cJ
    cC
    ctopon
    cfv
    wcel
    #
    cA
    cC
    wss
    #
    @23
    wph
    cJ
    ctop
    wcel
    #
    @25
    flfcntr.j
    cJ
    cC
    flfcntr.c
    toptopon
    sylib
    #
    flfcntr.a
    cA
    cJ
    cC
    resttopon
    syl2anc
    #
    wph
    cK
    ctop
    wcel
    #
    @24
    wph
    @21
    @30
    flfcntr.1
    cF
    @7
    cK
    cntop2
    syl
    cK
    cB
    flfcntr.b
    toptopon
    sylib
    vx
    va
    cF
    @7
    cK
    cA
    cB
    cnflf
    syl2anc
    mpbid
    simprd
    wph
    @17
    @9
    va
    @3
    @18
    wph
    cX
    cA
    cJ
    ccl
    cfv
    cfv
    #
    wcel
    #
    @3
    @18
    wcel
    #
    wph
    cA
    @31
    cX
    wph
    @27
    @26
    cA
    @31
    wss
    flfcntr.j
    flfcntr.a
    cA
    cJ
    cC
    flfcntr.c
    sscls
    syl2anc
    flfcntr.y
    sseldd
    wph
    @25
    @26
    cX
    cC
    wcel
    @32
    @33
    wb
    @28
    flfcntr.a
    wph
    cA
    cC
    cX
    flfcntr.a
    flfcntr.y
    sseldd
    cA
    cX
    cJ
    cC
    trnei
    syl3anc
    mpbid
    @12
    @3
    wceq
    #
    @17
    @9
    wb
    wph
    @34
    @15
    @6
    vx
    @16
    @8
    @12
    @3
    @7
    cflim
    oveq2
    @34
    @14
    @5
    @1
    @34
    cF
    @13
    @4
    @12
    @3
    cK
    cflf
    oveq2
    fveq1d
    eleq2d
    raleqbidv
    adantl
    rspcdv
    mpd
    wph
    @6
    @11
    vx
    cX
    @8
    wph
    cX
    @7
    @2
    @7
    cnei
    cfv
    cfv
    #
    cflim
    co
    #
    @8
    wph
    @23
    cX
    cA
    wcel
    cX
    @36
    wcel
    @29
    flfcntr.y
    cX
    @7
    cA
    neiflim
    syl2anc
    wph
    @35
    @3
    @7
    cflim
    wph
    @27
    @26
    @2
    cA
    wss
    @35
    @3
    wceq
    flfcntr.j
    flfcntr.a
    wph
    cX
    cA
    flfcntr.y
    snssd
    cA
    @2
    cJ
    cC
    flfcntr.c
    neitr
    syl3anc
    oveq2d
    eleqtrd
    @0
    cX
    wceq
    #
    @6
    @11
    wb
    wph
    @37
    @1
    @10
    @5
    @0
    cX
    cF
    fveq2
    eleq1d
    adantl
    rspcdv
    mpd
end
