include "wfn.mm"
include "crn.mm"
include "wss.mm"
include "wf.mm"
include "cuni.mm"
include "ccn.mm"
include "co.mm"
include "wcel.mm"
include "eqid.mm"
include "cnf.mm"
include "syl.mm"
include "ffn.mm"
include "frn.mm"
include "cconn.mm"
include "crest.mm"
include "wfo.mm"
include "dffn4.mm"
include "sylib.mm"
include "wceq.mm"
include "wb.mm"
include "ctop.mm"
include "cntop2.mm"
include "restuni.mm"
include "syl2anc.mm"
include "foeq3.mm"
include "mpbid.mm"
include "ctopon.mm"
include "cfv.mm"
include "toptopon.mm"
include "ssid.mm"
include "a1i.mm"
include "cnrest2.mm"
include "syl3anc.mm"
include "cnconn.mm"
include "cin.mm"
include "c0.mm"
include "wne.mm"
include "fnfvelrn.mm"
include "inelcm.mm"
include "connsubclo.mm"
include "df-f.mm"
include "sylanbrc.mm"

theorem conncn
  let wph: wff ph
  let cA: class A
  let cU: class U
  let cF: class F
  let cJ: class J
  let cK: class K
  let cX: class X
  assume conncn.x: |- X = U. J
  assume conncn.j: |- ( ph -> J e. Conn )
  assume conncn.f: |- ( ph -> F e. ( J Cn K ) )
  assume conncn.u: |- ( ph -> U e. K )
  assume conncn.c: |- ( ph -> U e. ( Clsd ` K ) )
  assume conncn.a: |- ( ph -> A e. X )
  assume conncn.1: |- ( ph -> ( F ` A ) e. U )


  assert |- ( ph -> F : X --> U )

  proof
    wph
    cF
    cX
    wfn
    #
    cF
    crn
    #
    cU
    wss
    cX
    cU
    cF
    wf
    wph
    cX
    cK
    cuni
    #
    cF
    wf
    #
    @0
    wph
    cF
    cJ
    cK
    ccn
    co
    wcel
    #
    @3
    conncn.f
    cF
    cJ
    cK
    cX
    @2
    conncn.x
    @2
    eqid
    #
    cnf
    syl
    #
    cX
    @2
    cF
    ffn
    syl
    #
    wph
    @1
    cU
    cK
    @2
    @5
    wph
    @3
    @1
    @2
    wss
    #
    @6
    cX
    @2
    cF
    frn
    syl
    #
    wph
    cJ
    cconn
    wcel
    cX
    cK
    @1
    crest
    co
    #
    cuni
    #
    cF
    wfo
    #
    cF
    cJ
    @10
    ccn
    co
    wcel
    #
    @10
    cconn
    wcel
    conncn.j
    wph
    cX
    @1
    cF
    wfo
    #
    @12
    wph
    @0
    @14
    @7
    cX
    cF
    dffn4
    sylib
    wph
    @1
    @11
    wceq
    #
    @14
    @12
    wb
    wph
    cK
    ctop
    wcel
    #
    @8
    @15
    wph
    @4
    @16
    conncn.f
    cF
    cJ
    cK
    cntop2
    syl
    #
    @9
    @1
    cK
    @2
    @5
    restuni
    syl2anc
    @1
    @11
    cX
    cF
    foeq3
    syl
    mpbid
    wph
    @4
    @13
    conncn.f
    wph
    cK
    @2
    ctopon
    cfv
    wcel
    #
    @1
    @1
    wss
    #
    @8
    @4
    @13
    wb
    wph
    @16
    @18
    @17
    cK
    @2
    @5
    toptopon
    sylib
    @19
    wph
    @1
    ssid
    a1i
    @9
    @1
    cF
    cJ
    cK
    @2
    cnrest2
    syl3anc
    mpbid
    cF
    cJ
    @10
    cX
    @11
    @11
    eqid
    cnconn
    syl3anc
    conncn.u
    wph
    cA
    cF
    cfv
    #
    cU
    wcel
    @20
    @1
    wcel
    #
    cU
    @1
    cin
    c0
    wne
    conncn.1
    wph
    @0
    cA
    cX
    wcel
    @21
    @7
    conncn.a
    cX
    cA
    cF
    fnfvelrn
    syl2anc
    @20
    cU
    @1
    inelcm
    syl2anc
    conncn.c
    connsubclo
    cX
    cU
    cF
    df-f
    sylanbrc
end
