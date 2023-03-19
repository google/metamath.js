include "ciun.mm"
include "cfv.mm"
include "cmpt.mm"
include "crn.mm"
include "cuni.mm"
include "cv.mm"
include "cesum.mm"
include "wcel.mm"
include "wral.mm"
include "wceq.mm"
include "ralrimiva.mm"
include "dfiun3g.mm"
include "syl.mm"
include "fveq2d.mm"
include "com.mm"
include "cdom.mm"
include "wbr.mm"
include "wss.mm"
include "wdisj.mm"
include "w3a.mm"
include "wa.mm"
include "mptct.mm"
include "rnct.mm"
include "3syl.mm"
include "eqid.mm"
include "rnmptss.mm"
include "disjrnmpt.mm"
include "3jca.mm"
include "ancli.mm"
include "cvv.mm"
include "wi.mm"
include "ctex.mm"
include "mptexg.mm"
include "rnexg.mm"
include "breq1.mm"
include "sseq1.mm"
include "disjeq1.mm"
include "3anbi123d.mm"
include "anbi2d.mm"
include "unieq.mm"
include "esumeq1.mm"
include "eqeq12d.mm"
include "imbi12d.mm"
include "vtoclg.mm"
include "mpd.mm"
include "fveq2.mm"
include "cc0.mm"
include "cpnf.mm"
include "cicc.mm"
include "co.mm"
include "wf.mm"
include "adantr.mm"
include "ffvelrnd.mm"
include "c0.mm"
include "adantl.mm"
include "ad2antrr.mm"
include "eqtrd.mm"
include "esumrnmpt2.mm"
include "3eqtrd.mm"

theorem pmeasadd
  let wph: wff ph
  let vx: setvar x
  let vy: setvar y
  let cA: class A
  let cB: class B
  let cP: class P
  let cQ: class Q
  let cR: class R
  let vk: setvar k
  let cO: class O
  let vs: setvar s
  assume caraext.1: |- ( ph -> P : R --> ( 0 [,] +oo ) )
  assume caraext.2: |- ( ph -> ( P ` (/) ) = 0 )
  assume caraext.3: |- ( ( ph /\ ( x ~<_ _om /\ x C_ R /\ Disj_ y e. x y ) ) -> ( P ` U. x ) = sum* y e. x ( P ` y ) )
  assume pmeassubadd.q: |- Q = { s e. ~P ~P O | ( (/) e. s /\ A. x e. s A. y e. s ( ( x u. y ) e. s /\ ( x \ y ) e. s ) ) }
  assume pmeassubadd.1: |- ( ph -> R e. Q )
  assume pmeassubadd.2: |- ( ph -> A ~<_ _om )
  assume pmeassubadd.3: |- ( ( ph /\ k e. A ) -> B e. R )
  assume pmeasadd.4: |- ( ph -> Disj_ k e. A B )

  disjoint A k
  disjoint A x
  disjoint A y
  disjoint k x
  disjoint k y
  disjoint x y
  disjoint B x
  disjoint B y
  disjoint P k
  disjoint P x
  disjoint P y
  disjoint R k
  disjoint R x
  disjoint R y
  disjoint k ph
  disjoint ph x
  disjoint ph y
  disjoint P x
  disjoint P y
  disjoint x y
  disjoint R x
  disjoint R y
  disjoint ph x
  disjoint ph y
  assert |- ( ph -> ( P ` U_ k e. A B ) = sum* k e. A ( P ` B ) )

  proof
    wph
    vk
    cA
    cB
    ciun
    #
    cP
    cfv
    vk
    cA
    cB
    cmpt
    #
    crn
    #
    cuni
    #
    cP
    cfv
    #
    @2
    vy
    cv
    #
    cP
    cfv
    #
    vy
    cesum
    #
    cA
    cB
    cP
    cfv
    #
    vk
    cesum
    wph
    @0
    @3
    cP
    wph
    cB
    cR
    wcel
    #
    vk
    cA
    wral
    #
    @0
    @3
    wceq
    wph
    @9
    vk
    cA
    pmeassubadd.3
    ralrimiva
    #
    vk
    cA
    cB
    cR
    dfiun3g
    syl
    fveq2d
    wph
    wph
    @2
    com
    cdom
    wbr
    #
    @2
    cR
    wss
    #
    vy
    @2
    @5
    wdisj
    #
    w3a
    #
    wa
    #
    @4
    @7
    wceq
    #
    wph
    @15
    wph
    @12
    @13
    @14
    wph
    cA
    com
    cdom
    wbr
    #
    @1
    com
    cdom
    wbr
    @12
    pmeassubadd.2
    vk
    cA
    cB
    mptct
    @1
    rnct
    3syl
    wph
    @10
    @13
    @11
    vk
    cA
    cB
    cR
    @1
    @1
    eqid
    rnmptss
    syl
    wph
    vk
    cA
    cB
    wdisj
    @14
    pmeasadd.4
    vk
    vy
    cA
    cB
    disjrnmpt
    syl
    3jca
    ancli
    wph
    @1
    cvv
    wcel
    #
    @2
    cvv
    wcel
    @16
    @17
    wi
    #
    wph
    @18
    cA
    cvv
    wcel
    #
    @19
    pmeassubadd.2
    cA
    ctex
    #
    vk
    cA
    cB
    cvv
    mptexg
    3syl
    @1
    cvv
    rnexg
    wph
    vx
    cv
    #
    com
    cdom
    wbr
    #
    @23
    cR
    wss
    #
    vy
    @23
    @5
    wdisj
    #
    w3a
    #
    wa
    #
    @23
    cuni
    #
    cP
    cfv
    #
    @23
    @6
    vy
    cesum
    #
    wceq
    #
    wi
    @20
    vx
    @2
    cvv
    @23
    @2
    wceq
    #
    @28
    @16
    @32
    @17
    @33
    @27
    @15
    wph
    @33
    @24
    @12
    @25
    @13
    @26
    @14
    @23
    @2
    com
    cdom
    breq1
    @23
    @2
    cR
    sseq1
    vy
    @23
    @2
    @5
    disjeq1
    3anbi123d
    anbi2d
    @33
    @30
    @4
    @31
    @7
    @33
    @29
    @3
    cP
    @23
    @2
    unieq
    fveq2d
    @23
    @2
    @6
    vy
    esumeq1
    eqeq12d
    imbi12d
    caraext.3
    vtoclg
    3syl
    mpd
    wph
    vy
    cA
    cB
    @6
    @8
    vk
    cvv
    cR
    @5
    cB
    cP
    fveq2
    wph
    @18
    @21
    pmeassubadd.2
    @22
    syl
    wph
    vk
    cv
    cA
    wcel
    #
    wa
    #
    cR
    cc0
    cpnf
    cicc
    co
    #
    cB
    cP
    wph
    cR
    @36
    cP
    wf
    @34
    caraext.1
    adantr
    pmeassubadd.3
    ffvelrnd
    pmeassubadd.3
    @35
    cB
    c0
    wceq
    #
    wa
    @8
    c0
    cP
    cfv
    #
    cc0
    @37
    @8
    @38
    wceq
    @35
    cB
    c0
    cP
    fveq2
    adantl
    wph
    @38
    cc0
    wceq
    @34
    @37
    caraext.2
    ad2antrr
    eqtrd
    pmeasadd.4
    esumrnmpt2
    3eqtrd
end
