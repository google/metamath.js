include "ccn.mm"
include "co.mm"
include "wcel.mm"
include "wf.mm"
include "ccnv.mm"
include "cv.mm"
include "cima.mm"
include "ccld.mm"
include "cfv.mm"
include "wral.mm"
include "wa.mm"
include "cres.mm"
include "cun.mm"
include "wceq.mm"
include "cin.mm"
include "ineq2d.mm"
include "wfun.mm"
include "ffun.mm"
include "syl.mm"
include "respreima.mm"
include "uneq12d.mm"
include "indi.mm"
include "syl6reqr.mm"
include "wss.mm"
include "crn.mm"
include "imassrn.mm"
include "cdm.mm"
include "dfdm4.mm"
include "fdm.mm"
include "syl5eqr.mm"
include "syl5sseq.mm"
include "df-ss.mm"
include "sylib.mm"
include "3eqtr3rd.mm"
include "adantr.mm"
include "crest.mm"
include "cnclima.mm"
include "sylan.mm"
include "restcldr.mm"
include "syl2anc.mm"
include "uncld.mm"
include "eqeltrd.mm"
include "ralrimiva.mm"
include "ctop.mm"
include "wb.mm"
include "cldrcl.mm"
include "cntop2.mm"
include "ctopon.mm"
include "toptopon.mm"
include "iscncl.mm"
include "syl2anb.mm"
include "mpbir2and.mm"

theorem paste
  let wph: wff ph
  let cA: class A
  let cB: class B
  let cF: class F
  let cJ: class J
  let cK: class K
  let cX: class X
  let cY: class Y
  let vy: setvar y
  assume paste.1: |- X = U. J
  assume paste.2: |- Y = U. K
  assume paste.4: |- ( ph -> A e. ( Clsd ` J ) )
  assume paste.5: |- ( ph -> B e. ( Clsd ` J ) )
  assume paste.6: |- ( ph -> ( A u. B ) = X )
  assume paste.7: |- ( ph -> F : X --> Y )
  assume paste.8: |- ( ph -> ( F |` A ) e. ( ( J |`t A ) Cn K ) )
  assume paste.9: |- ( ph -> ( F |` B ) e. ( ( J |`t B ) Cn K ) )


  assert |- ( ph -> F e. ( J Cn K ) )

  proof
    wph
    cF
    cJ
    cK
    ccn
    co
    wcel
    #
    cX
    cY
    cF
    wf
    #
    cF
    ccnv
    #
    vy
    cv
    #
    cima
    #
    cJ
    ccld
    cfv
    #
    wcel
    #
    vy
    cK
    ccld
    cfv
    #
    wral
    #
    paste.7
    wph
    @6
    vy
    @7
    wph
    @3
    @7
    wcel
    #
    wa
    #
    @4
    cF
    cA
    cres
    #
    ccnv
    @3
    cima
    #
    cF
    cB
    cres
    #
    ccnv
    @3
    cima
    #
    cun
    #
    @5
    wph
    @4
    @15
    wceq
    @9
    wph
    @4
    cA
    cB
    cun
    #
    cin
    #
    @4
    cX
    cin
    #
    @15
    @4
    wph
    @16
    cX
    @4
    paste.6
    ineq2d
    wph
    @15
    @4
    cA
    cin
    #
    @4
    cB
    cin
    #
    cun
    #
    @17
    wph
    cF
    wfun
    #
    @15
    @21
    wceq
    wph
    @1
    @22
    paste.7
    cX
    cY
    cF
    ffun
    syl
    @22
    @12
    @19
    @14
    @20
    @3
    cA
    cF
    respreima
    @3
    cB
    cF
    respreima
    uneq12d
    syl
    @4
    cA
    cB
    indi
    syl6reqr
    wph
    @4
    cX
    wss
    #
    @18
    @4
    wceq
    wph
    @1
    @23
    paste.7
    @1
    @2
    crn
    #
    @4
    cX
    @2
    @3
    imassrn
    @1
    @24
    cF
    cdm
    cX
    cF
    dfdm4
    cX
    cY
    cF
    fdm
    syl5eqr
    syl5sseq
    syl
    @4
    cX
    df-ss
    sylib
    3eqtr3rd
    adantr
    @10
    @12
    @5
    wcel
    #
    @14
    @5
    wcel
    #
    @15
    @5
    wcel
    @10
    cA
    @5
    wcel
    #
    @12
    cJ
    cA
    crest
    co
    #
    ccld
    cfv
    wcel
    #
    @25
    wph
    @27
    @9
    paste.4
    adantr
    wph
    @11
    @28
    cK
    ccn
    co
    wcel
    #
    @9
    @29
    paste.8
    @3
    @11
    @28
    cK
    cnclima
    sylan
    cA
    @12
    cJ
    restcldr
    syl2anc
    @10
    cB
    @5
    wcel
    #
    @14
    cJ
    cB
    crest
    co
    #
    ccld
    cfv
    wcel
    #
    @26
    wph
    @31
    @9
    paste.5
    adantr
    wph
    @13
    @32
    cK
    ccn
    co
    wcel
    @9
    @33
    paste.9
    @3
    @13
    @32
    cK
    cnclima
    sylan
    cB
    @14
    cJ
    restcldr
    syl2anc
    @12
    @14
    cJ
    uncld
    syl2anc
    eqeltrd
    ralrimiva
    wph
    cJ
    ctop
    wcel
    #
    cK
    ctop
    wcel
    #
    @0
    @1
    @8
    wa
    wb
    #
    wph
    @27
    @34
    paste.4
    cA
    cJ
    cldrcl
    syl
    wph
    @30
    @35
    paste.8
    @11
    @28
    cK
    cntop2
    syl
    @34
    cJ
    cX
    ctopon
    cfv
    wcel
    cK
    cY
    ctopon
    cfv
    wcel
    @36
    @35
    cJ
    cX
    paste.1
    toptopon
    cK
    cY
    paste.2
    toptopon
    vy
    cF
    cJ
    cK
    cX
    cY
    iscncl
    syl2anb
    syl2anc
    mpbir2and
end
