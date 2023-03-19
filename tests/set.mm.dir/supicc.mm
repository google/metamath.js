include "cr.mm"
include "clt.mm"
include "csup.mm"
include "cicc.mm"
include "co.mm"
include "wcel.mm"
include "cle.mm"
include "wbr.mm"
include "wss.mm"
include "c0.mm"
include "wne.mm"
include "cv.mm"
include "wral.mm"
include "wrex.mm"
include "iccssre.mm"
include "syl2anc.mm"
include "sstrd.mm"
include "wa.mm"
include "cxr.mm"
include "adantr.mm"
include "rexrd.mm"
include "sselda.mm"
include "iccleub.mm"
include "syl3anc.mm"
include "ralrimiva.mm"
include "wceq.mm"
include "breq2.mm"
include "ralbidv.mm"
include "rspcev.mm"
include "suprcl.mm"
include "w3a.mm"
include "simpr.mm"
include "iccsupr.mm"
include "syl211anc.mm"
include "syl.mm"
include "iccgelb.mm"
include "suprub.mm"
include "letrd.mm"
include "wb.mm"
include "r19.3rzv.mm"
include "mpbird.mm"
include "suprleub.mm"
include "syl31anc.mm"
include "elicc2.mm"
include "mpbir3and.mm"

theorem supicc
  let wph: wff ph
  let cA: class A
  let cB: class B
  let cC: class C
  let vx: setvar x
  let vy: setvar y
  assume supicc.1: |- ( ph -> B e. RR )
  assume supicc.2: |- ( ph -> C e. RR )
  assume supicc.3: |- ( ph -> A C_ ( B [,] C ) )
  assume supicc.4: |- ( ph -> A =/= (/) )


  assert |- ( ph -> sup ( A , RR , < ) e. ( B [,] C ) )

  proof
    wph
    cA
    cr
    clt
    csup
    #
    cB
    cC
    cicc
    co
    #
    wcel
    #
    @0
    cr
    wcel
    #
    cB
    @0
    cle
    wbr
    #
    @0
    cC
    cle
    wbr
    #
    wph
    cA
    cr
    wss
    #
    cA
    c0
    wne
    #
    vx
    cv
    #
    vy
    cv
    #
    cle
    wbr
    #
    vx
    cA
    wral
    #
    vy
    cr
    wrex
    #
    @3
    wph
    cA
    @1
    cr
    supicc.3
    wph
    cB
    cr
    wcel
    #
    cC
    cr
    wcel
    #
    @1
    cr
    wss
    supicc.1
    supicc.2
    cB
    cC
    iccssre
    syl2anc
    sstrd
    #
    supicc.4
    wph
    @14
    @8
    cC
    cle
    wbr
    #
    vx
    cA
    wral
    #
    @12
    supicc.2
    wph
    @16
    vx
    cA
    wph
    @8
    cA
    wcel
    #
    wa
    #
    cB
    cxr
    wcel
    #
    cC
    cxr
    wcel
    #
    @8
    @1
    wcel
    #
    @16
    @19
    cB
    wph
    @13
    @18
    supicc.1
    adantr
    #
    rexrd
    #
    @19
    cC
    wph
    @14
    @18
    supicc.2
    adantr
    #
    rexrd
    #
    wph
    cA
    @1
    @8
    supicc.3
    sselda
    #
    cB
    cC
    @8
    iccleub
    syl3anc
    ralrimiva
    #
    @11
    @17
    vy
    cC
    cr
    @9
    cC
    wceq
    @10
    @16
    vx
    cA
    @9
    cC
    @8
    cle
    breq2
    ralbidv
    rspcev
    syl2anc
    #
    vy
    vx
    cA
    suprcl
    #
    syl3anc
    wph
    @4
    @4
    vx
    cA
    wral
    #
    wph
    @4
    vx
    cA
    @19
    cB
    @8
    @0
    @23
    wph
    cA
    cr
    @8
    @15
    sselda
    @19
    @6
    @7
    @12
    w3a
    #
    @3
    @19
    @13
    @14
    cA
    @1
    wss
    #
    @18
    @32
    @23
    @25
    wph
    @33
    @18
    supicc.3
    adantr
    wph
    @18
    simpr
    #
    vy
    vx
    cB
    cC
    @8
    cA
    iccsupr
    syl211anc
    #
    @30
    syl
    @19
    @20
    @21
    @22
    cB
    @8
    cle
    wbr
    @24
    @26
    @27
    cB
    cC
    @8
    iccgelb
    syl3anc
    @19
    @32
    @18
    @8
    @0
    cle
    wbr
    @35
    @34
    vy
    vx
    cA
    @8
    suprub
    syl2anc
    letrd
    ralrimiva
    wph
    @7
    @4
    @31
    wb
    supicc.4
    @4
    vx
    cA
    r19.3rzv
    syl
    mpbird
    wph
    @5
    @17
    @28
    wph
    @6
    @7
    @12
    @14
    @5
    @17
    wb
    @15
    supicc.4
    @29
    supicc.2
    vy
    vx
    vx
    cA
    cC
    suprleub
    syl31anc
    mpbird
    wph
    @13
    @14
    @2
    @3
    @4
    @5
    w3a
    wb
    supicc.1
    supicc.2
    cB
    cC
    @0
    elicc2
    syl2anc
    mpbir3and
end
