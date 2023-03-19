include "nfv.mm"
include "ctop.mm"
include "wcel.mm"
include "cioo.mm"
include "crn.mm"
include "ctg.mm"
include "cfv.mm"
include "retop.mm"
include "eqeltri.mm"
include "a1i.mm"
include "salgencld.mm"
include "cr.mm"
include "cuni.mm"
include "unisalgen2.mm"
include "wceq.mm"
include "unieqi.mm"
include "uniretop.mm"
include "eqcomi.mm"
include "3eqtrrd.mm"
include "sseqtrd.mm"
include "cv.mm"
include "wa.mm"
include "clt.mm"
include "wbr.mm"
include "crab.mm"
include "crest.mm"
include "co.mm"
include "cin.mm"
include "wrex.mm"
include "cxr.mm"
include "csup.mm"
include "cmnf.mm"
include "cioc.mm"
include "wss.mm"
include "adantr.mm"
include "wf.mm"
include "frexr.mm"
include "cle.mm"
include "wi.mm"
include "wral.mm"
include "breq1.mm"
include "fveq2.mm"
include "breq1d.mm"
include "imbi12d.mm"
include "breq2.mm"
include "breq2d.mm"
include "cbvral2v.mm"
include "sylib.mm"
include "rexr.mm"
include "adantl.mm"
include "cbvrabv.mm"
include "eqid.mm"
include "incsmflem.mm"
include "wb.mm"
include "csalg.mm"
include "cvv.mm"
include "reex.mm"
include "ssexd.mm"
include "elrest.mm"
include "syl2anc.mm"
include "mpbird.mm"
include "issmfd.mm"

theorem incsmf
  let wph: wff ph
  let vx: setvar x
  let vy: setvar y
  let cA: class A
  let cB: class B
  let cF: class F
  let cJ: class J
  let vb: setvar b
  let vw: setvar w
  let vz: setvar z
  let va: setvar a
  let vk: setvar k
  assume incsmf.a: |- ( ph -> A C_ RR )
  assume incsmf.f: |- ( ph -> F : A --> RR )
  assume incsmf.i: |- ( ph -> A. x e. A A. y e. A ( x <_ y -> ( F ` x ) <_ ( F ` y ) ) )
  assume incsmf.j: |- J = ( topGen ` ran (,) )
  assume incsmf.b: |- B = ( SalGen ` J )

  disjoint A x
  disjoint A y
  disjoint x y
  disjoint F x
  disjoint F y
  disjoint A b
  disjoint b x
  disjoint A w
  disjoint A z
  disjoint w x
  disjoint w y
  disjoint w z
  disjoint x z
  disjoint y z
  disjoint B a
  disjoint B b
  disjoint a b
  disjoint F a
  disjoint F b
  disjoint a x
  disjoint F w
  disjoint F z
  disjoint a w
  disjoint a z
  disjoint a ph
  disjoint ph w
  disjoint ph z
  disjoint k x
  assert |- ( ph -> F e. ( SMblFn ` B ) )

  proof
    wph
    vx
    cA
    cB
    cF
    va
    wph
    va
    nfv
    wph
    cB
    ctop
    cJ
    cJ
    ctop
    wcel
    wph
    cJ
    cioo
    crn
    ctg
    cfv
    #
    ctop
    incsmf.j
    retop
    eqeltri
    a1i
    #
    incsmf.b
    salgencld
    #
    wph
    cA
    cr
    cB
    cuni
    #
    incsmf.a
    wph
    @3
    cJ
    cuni
    #
    @0
    cuni
    #
    cr
    wph
    cJ
    cB
    ctop
    @1
    incsmf.b
    unisalgen2
    @4
    @5
    wceq
    wph
    cJ
    @0
    incsmf.j
    unieqi
    a1i
    @5
    cr
    wceq
    wph
    cr
    @5
    uniretop
    eqcomi
    a1i
    3eqtrrd
    sseqtrd
    incsmf.f
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
    #
    cF
    cfv
    #
    @6
    clt
    wbr
    #
    vx
    cA
    crab
    #
    cB
    cA
    crest
    co
    wcel
    #
    @12
    vb
    cv
    cA
    cin
    wceq
    vb
    cB
    wrex
    #
    @8
    vw
    vz
    cA
    cB
    @12
    cxr
    clt
    csup
    #
    cmnf
    @15
    cioo
    co
    #
    @6
    cmnf
    @15
    cioc
    co
    #
    cF
    cJ
    @12
    vb
    @8
    vw
    nfv
    @8
    vz
    nfv
    wph
    cA
    cr
    wss
    @7
    incsmf.a
    adantr
    wph
    cA
    cxr
    cF
    wf
    @7
    wph
    cA
    cF
    incsmf.f
    frexr
    adantr
    wph
    vw
    cv
    #
    vz
    cv
    #
    cle
    wbr
    #
    @18
    cF
    cfv
    #
    @19
    cF
    cfv
    #
    cle
    wbr
    #
    wi
    #
    vz
    cA
    wral
    vw
    cA
    wral
    #
    @7
    wph
    @9
    vy
    cv
    #
    cle
    wbr
    #
    @10
    @26
    cF
    cfv
    #
    cle
    wbr
    #
    wi
    #
    vy
    cA
    wral
    vx
    cA
    wral
    @25
    incsmf.i
    @30
    @24
    @18
    @26
    cle
    wbr
    #
    @21
    @28
    cle
    wbr
    #
    wi
    vx
    vy
    vw
    vz
    cA
    cA
    @9
    @18
    wceq
    #
    @27
    @31
    @29
    @32
    @9
    @18
    @26
    cle
    breq1
    @33
    @10
    @21
    @28
    cle
    @9
    @18
    cF
    fveq2
    #
    breq1d
    imbi12d
    @26
    @19
    wceq
    #
    @31
    @20
    @32
    @23
    @26
    @19
    @18
    cle
    breq2
    @35
    @28
    @22
    @21
    cle
    @26
    @19
    cF
    fveq2
    breq2d
    imbi12d
    cbvral2v
    sylib
    adantr
    incsmf.j
    incsmf.b
    @7
    @6
    cxr
    wcel
    wph
    @6
    rexr
    adantl
    @11
    @21
    @6
    clt
    wbr
    vx
    vw
    cA
    @33
    @10
    @21
    @6
    clt
    @34
    breq1d
    cbvrabv
    @15
    eqid
    @16
    eqid
    @17
    eqid
    incsmflem
    wph
    @13
    @14
    wb
    #
    @7
    wph
    cB
    csalg
    wcel
    cA
    cvv
    wcel
    @36
    @2
    wph
    cA
    cr
    cvv
    cr
    cvv
    wcel
    wph
    reex
    a1i
    incsmf.a
    ssexd
    vb
    @12
    cA
    cB
    csalg
    cvv
    elrest
    syl2anc
    adantr
    mpbird
    issmfd
end
