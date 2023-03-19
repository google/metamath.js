include "crest.mm"
include "co.mm"
include "cconn.mm"
include "wcel.mm"
include "cima.mm"
include "cuni.mm"
include "cres.mm"
include "wfo.mm"
include "ccn.mm"
include "wfun.mm"
include "cdm.mm"
include "wss.mm"
include "wf.mm"
include "eqid.mm"
include "cnf.mm"
include "syl.mm"
include "ffun.mm"
include "wceq.mm"
include "fdm.mm"
include "sseqtr4d.mm"
include "fores.mm"
include "syl2anc.mm"
include "wb.mm"
include "ctop.mm"
include "cntop2.mm"
include "crn.mm"
include "imassrn.mm"
include "frn.mm"
include "syl5ss.mm"
include "restuni.mm"
include "foeq3.mm"
include "mpbid.mm"
include "cnrest.mm"
include "ctopon.mm"
include "cfv.mm"
include "toptopon.mm"
include "sylib.mm"
include "df-ima.mm"
include "eqimss2.mm"
include "mp1i.mm"
include "cnrest2.mm"
include "syl3anc.mm"
include "cnconn.mm"

theorem connima
  let wph: wff ph
  let cA: class A
  let cF: class F
  let cJ: class J
  let cK: class K
  let cX: class X
  assume connima.x: |- X = U. J
  assume connima.f: |- ( ph -> F e. ( J Cn K ) )
  assume connima.a: |- ( ph -> A C_ X )
  assume connima.c: |- ( ph -> ( J |`t A ) e. Conn )


  assert |- ( ph -> ( K |`t ( F " A ) ) e. Conn )

  proof
    wph
    cJ
    cA
    crest
    co
    #
    cconn
    wcel
    cA
    cK
    cF
    cA
    cima
    #
    crest
    co
    #
    cuni
    #
    cF
    cA
    cres
    #
    wfo
    #
    @4
    @0
    @2
    ccn
    co
    wcel
    #
    @2
    cconn
    wcel
    connima.c
    wph
    cA
    @1
    @4
    wfo
    #
    @5
    wph
    cF
    wfun
    #
    cA
    cF
    cdm
    #
    wss
    @7
    wph
    cX
    cK
    cuni
    #
    cF
    wf
    #
    @8
    wph
    cF
    cJ
    cK
    ccn
    co
    wcel
    #
    @11
    connima.f
    cF
    cJ
    cK
    cX
    @10
    connima.x
    @10
    eqid
    #
    cnf
    syl
    #
    cX
    @10
    cF
    ffun
    syl
    wph
    cA
    cX
    @9
    connima.a
    wph
    @11
    @9
    cX
    wceq
    @14
    cX
    @10
    cF
    fdm
    syl
    sseqtr4d
    cA
    cF
    fores
    syl2anc
    wph
    @1
    @3
    wceq
    #
    @7
    @5
    wb
    wph
    cK
    ctop
    wcel
    #
    @1
    @10
    wss
    #
    @15
    wph
    @12
    @16
    connima.f
    cF
    cJ
    cK
    cntop2
    syl
    #
    wph
    @1
    cF
    crn
    #
    @10
    cF
    cA
    imassrn
    wph
    @11
    @19
    @10
    wss
    @14
    cX
    @10
    cF
    frn
    syl
    syl5ss
    #
    @1
    cK
    @10
    @13
    restuni
    syl2anc
    @1
    @3
    cA
    @4
    foeq3
    syl
    mpbid
    wph
    @4
    @0
    cK
    ccn
    co
    wcel
    #
    @6
    wph
    @12
    cA
    cX
    wss
    @21
    connima.f
    connima.a
    cA
    cF
    cJ
    cK
    cX
    connima.x
    cnrest
    syl2anc
    wph
    cK
    @10
    ctopon
    cfv
    wcel
    #
    @4
    crn
    #
    @1
    wss
    #
    @17
    @21
    @6
    wb
    wph
    @16
    @22
    @18
    cK
    @10
    @13
    toptopon
    sylib
    @1
    @23
    wceq
    @24
    wph
    cF
    cA
    df-ima
    @23
    @1
    eqimss2
    mp1i
    @20
    @1
    @4
    @0
    cK
    @10
    cnrest2
    syl3anc
    mpbid
    @4
    @0
    @2
    cA
    @3
    @3
    eqid
    cnconn
    syl3anc
end
