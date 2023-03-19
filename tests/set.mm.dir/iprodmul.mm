include "cmul.mm"
include "co.mm"
include "cprod.mm"
include "cv.mm"
include "cfv.mm"
include "cmpt.mm"
include "cc0.mm"
include "wne.mm"
include "cseq.mm"
include "cli.mm"
include "wbr.mm"
include "wa.mm"
include "wex.mm"
include "wrex.mm"
include "wcel.mm"
include "cc.mm"
include "eqeltrd.mm"
include "wceq.mm"
include "weq.mm"
include "fveq2.mm"
include "oveq12d.mm"
include "eqid.mm"
include "ovex.mm"
include "fvmpt.mm"
include "adantl.mm"
include "ntrivcvgmul.mm"
include "cbvmptv.mm"
include "seqeq3.mm"
include "ax-mp.mm"
include "breq1i.mm"
include "anbi2i.mm"
include "exbii.mm"
include "rexbii.mm"
include "sylibr.mm"
include "simpr.mm"
include "mulcld.mm"
include "fvmptg.mm"
include "syl2anc.mm"
include "eqtrd.mm"
include "cvv.mm"
include "iprodclim2.mm"
include "seqex.mm"
include "a1i.mm"
include "prodf.mm"
include "ffvelrnda.mm"
include "cuz.mm"
include "syl6eleq.mm"
include "cfz.mm"
include "elfzuz.mm"
include "syl6eleqr.mm"
include "sylan2.mm"
include "adantlr.mm"
include "prodfmul.mm"
include "climmul.mm"
include "iprodclim.mm"

theorem iprodmul
  let wph: wff ph
  let vy: setvar y
  let vz: setvar z
  let cA: class A
  let cB: class B
  let vk: setvar k
  let vm: setvar m
  let vn: setvar n
  let cF: class F
  let cG: class G
  let cM: class M
  let cZ: class Z
  let vj: setvar j
  let va: setvar a
  let vp: setvar p
  let vw: setvar w
  assume iprodmul.1: |- Z = ( ZZ>= ` M )
  assume iprodmul.2: |- ( ph -> M e. ZZ )
  assume iprodmul.3: |- ( ph -> E. n e. Z E. y ( y =/= 0 /\ seq n ( x. , F ) ~~> y ) )
  assume iprodmul.4: |- ( ( ph /\ k e. Z ) -> ( F ` k ) = A )
  assume iprodmul.5: |- ( ( ph /\ k e. Z ) -> A e. CC )
  assume iprodmul.6: |- ( ph -> E. m e. Z E. z ( z =/= 0 /\ seq m ( x. , G ) ~~> z ) )
  assume iprodmul.7: |- ( ( ph /\ k e. Z ) -> ( G ` k ) = B )
  assume iprodmul.8: |- ( ( ph /\ k e. Z ) -> B e. CC )

  disjoint A n
  disjoint A y
  disjoint B m
  disjoint B z
  disjoint F k
  disjoint F m
  disjoint F n
  disjoint F y
  disjoint F z
  disjoint G k
  disjoint G m
  disjoint G n
  disjoint G y
  disjoint G z
  disjoint k m
  disjoint k n
  disjoint k ph
  disjoint k y
  disjoint k z
  disjoint M k
  disjoint M m
  disjoint m n
  disjoint M n
  disjoint m ph
  disjoint m y
  disjoint M y
  disjoint m z
  disjoint M z
  disjoint n ph
  disjoint n y
  disjoint n z
  disjoint ph y
  disjoint ph z
  disjoint y z
  disjoint Z k
  disjoint Z m
  disjoint Z n
  disjoint Z y
  disjoint Z z
  disjoint A j
  disjoint a k
  disjoint a m
  disjoint a n
  disjoint A p
  disjoint A w
  disjoint a y
  disjoint a z
  disjoint B j
  disjoint B p
  disjoint B w
  disjoint F a
  disjoint F j
  disjoint G a
  disjoint G j
  disjoint j k
  disjoint j m
  disjoint j ph
  disjoint k p
  disjoint k w
  disjoint M j
  disjoint m p
  disjoint m w
  disjoint M w
  disjoint n p
  disjoint n w
  disjoint p ph
  disjoint p w
  disjoint p y
  disjoint p z
  disjoint ph w
  disjoint w y
  disjoint w z
  disjoint Z a
  disjoint Z j
  disjoint Z p
  disjoint Z w
  disjoint a p
  disjoint a w
  disjoint F p
  disjoint F w
  disjoint G p
  disjoint G w
  assert |- ( ph -> prod_ k e. Z ( A x. B ) = ( prod_ k e. Z A x. prod_ k e. Z B ) )

  proof
    wph
    vw
    cA
    cB
    cmul
    co
    #
    cZ
    cA
    vk
    cprod
    #
    cZ
    cB
    vk
    cprod
    #
    cmul
    co
    vk
    vp
    vm
    cZ
    vm
    cv
    #
    cF
    cfv
    #
    @3
    cG
    cfv
    #
    cmul
    co
    #
    cmpt
    #
    cM
    cZ
    iprodmul.1
    iprodmul.2
    wph
    vw
    cv
    #
    cc0
    wne
    #
    cmul
    va
    cZ
    va
    cv
    #
    cF
    cfv
    #
    @10
    cG
    cfv
    #
    cmul
    co
    #
    cmpt
    #
    vp
    cv
    #
    cseq
    #
    @8
    cli
    wbr
    #
    wa
    #
    vw
    wex
    #
    vp
    cZ
    wrex
    @9
    cmul
    @7
    @15
    cseq
    #
    @8
    cli
    wbr
    #
    wa
    #
    vw
    wex
    #
    vp
    cZ
    wrex
    wph
    vy
    vz
    vw
    vk
    vm
    vn
    cF
    cG
    @14
    cM
    cZ
    vp
    iprodmul.1
    iprodmul.3
    wph
    vk
    cv
    #
    cZ
    wcel
    #
    wa
    #
    @24
    cF
    cfv
    #
    cA
    cc
    iprodmul.4
    iprodmul.5
    eqeltrd
    #
    iprodmul.6
    @26
    @24
    cG
    cfv
    #
    cB
    cc
    iprodmul.7
    iprodmul.8
    eqeltrd
    #
    @25
    @24
    @14
    cfv
    @27
    @29
    cmul
    co
    #
    wceq
    wph
    va
    @24
    @13
    @31
    cZ
    @14
    va
    vk
    weq
    @11
    @27
    @12
    @29
    cmul
    @10
    @24
    cF
    fveq2
    @10
    @24
    cG
    fveq2
    oveq12d
    @14
    eqid
    @27
    @29
    cmul
    ovex
    fvmpt
    adantl
    ntrivcvgmul
    @23
    @19
    vp
    cZ
    @22
    @18
    vw
    @21
    @17
    @9
    @20
    @16
    @8
    cli
    @7
    @14
    wceq
    @20
    @16
    wceq
    vm
    va
    cZ
    @6
    @13
    vm
    va
    weq
    @4
    @11
    @5
    @12
    cmul
    @3
    @10
    cF
    fveq2
    @3
    @10
    cG
    fveq2
    oveq12d
    cbvmptv
    cmul
    @7
    @14
    @15
    seqeq3
    ax-mp
    breq1i
    anbi2i
    exbii
    rexbii
    sylibr
    @26
    @24
    @7
    cfv
    #
    @31
    @0
    @26
    @25
    @31
    cc
    wcel
    @32
    @31
    wceq
    #
    wph
    @25
    simpr
    @26
    @27
    @29
    @28
    @30
    mulcld
    vm
    @24
    @6
    @31
    cZ
    cc
    @7
    vm
    vk
    weq
    @4
    @27
    @5
    @29
    cmul
    @3
    @24
    cF
    fveq2
    @3
    @24
    cG
    fveq2
    oveq12d
    @7
    eqid
    fvmptg
    syl2anc
    #
    @26
    @27
    cA
    @29
    cB
    cmul
    iprodmul.4
    iprodmul.7
    oveq12d
    eqtrd
    @26
    cA
    cB
    iprodmul.5
    iprodmul.8
    mulcld
    wph
    @1
    @2
    vj
    cmul
    cF
    cM
    cseq
    #
    cmul
    cG
    cM
    cseq
    #
    cmul
    @7
    cM
    cseq
    #
    cM
    cvv
    cZ
    iprodmul.1
    iprodmul.2
    wph
    vy
    cA
    vk
    vn
    cF
    cM
    cZ
    iprodmul.1
    iprodmul.2
    iprodmul.3
    iprodmul.4
    iprodmul.5
    iprodclim2
    @37
    cvv
    wcel
    wph
    cmul
    @7
    cM
    seqex
    a1i
    wph
    vz
    cB
    vk
    vm
    cG
    cM
    cZ
    iprodmul.1
    iprodmul.2
    iprodmul.6
    iprodmul.7
    iprodmul.8
    iprodclim2
    wph
    cZ
    cc
    vj
    cv
    #
    @35
    wph
    vk
    cF
    cM
    cZ
    iprodmul.1
    iprodmul.2
    @28
    prodf
    ffvelrnda
    wph
    cZ
    cc
    @38
    @36
    wph
    vk
    cG
    cM
    cZ
    iprodmul.1
    iprodmul.2
    @30
    prodf
    ffvelrnda
    wph
    @38
    cZ
    wcel
    #
    wa
    #
    vk
    cF
    cG
    @7
    cM
    @38
    @40
    @38
    cZ
    cM
    cuz
    cfv
    #
    wph
    @39
    simpr
    iprodmul.1
    syl6eleq
    wph
    @24
    cM
    @38
    cfz
    co
    wcel
    #
    @27
    cc
    wcel
    #
    @39
    @42
    wph
    @25
    @43
    @42
    @24
    @41
    cZ
    @24
    cM
    @38
    elfzuz
    iprodmul.1
    syl6eleqr
    #
    @28
    sylan2
    adantlr
    wph
    @42
    @29
    cc
    wcel
    #
    @39
    @42
    wph
    @25
    @45
    @44
    @30
    sylan2
    adantlr
    @42
    @40
    @25
    @33
    @44
    wph
    @25
    @33
    @39
    @34
    adantlr
    sylan2
    prodfmul
    climmul
    iprodclim
end
