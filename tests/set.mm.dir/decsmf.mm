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
include "nfan.mm"
include "wss.mm"
include "adantr.mm"
include "wf.mm"
include "frexr.mm"
include "cle.mm"
include "wi.mm"
include "wral.mm"
include "breq1.mm"
include "fveq2.mm"
include "breq2d.mm"
include "imbi12d.mm"
include "breq2.mm"
include "breq1d.mm"
include "cbvral2v.mm"
include "sylib.mm"
include "sylibr.mm"
include "rexr.mm"
include "adantl.mm"
include "eqid.mm"
include "cbvrabv.mm"
include "supeq1i.mm"
include "decsmflem.mm"
include "wb.mm"
include "cvv.mm"
include "csalg.mm"
include "elexd.mm"
include "reex.mm"
include "ssexd.mm"
include "elrest.mm"
include "syl2anc.mm"
include "mpbird.mm"
include "issmfgtd.mm"

theorem decsmf
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
  assume decsmf.x: |- F/ x ph
  assume decsmf.y: |- F/ y ph
  assume decsmf.a: |- ( ph -> A C_ RR )
  assume decsmf.f: |- ( ph -> F : A --> RR )
  assume decsmf.i: |- ( ph -> A. x e. A A. y e. A ( x <_ y -> ( F ` y ) <_ ( F ` x ) ) )
  assume decsmf.j: |- J = ( topGen ` ran (,) )
  assume decsmf.b: |- B = ( SalGen ` J )

  disjoint A x
  disjoint A y
  disjoint x y
  disjoint F x
  disjoint F y
  disjoint A b
  disjoint A w
  disjoint b w
  disjoint b x
  disjoint w x
  disjoint w y
  disjoint A z
  disjoint w z
  disjoint y z
  disjoint B a
  disjoint B b
  disjoint a b
  disjoint F a
  disjoint F b
  disjoint F w
  disjoint a w
  disjoint a x
  disjoint a y
  disjoint F z
  disjoint a ph
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
    decsmf.j
    retop
    eqeltri
    a1i
    #
    decsmf.b
    salgencld
    #
    wph
    cA
    cr
    cB
    cuni
    #
    decsmf.a
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
    decsmf.b
    unisalgen2
    @4
    @5
    wceq
    wph
    cJ
    @0
    decsmf.j
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
    decsmf.f
    wph
    va
    cv
    #
    cr
    wcel
    #
    wa
    #
    @6
    vx
    cv
    #
    cF
    cfv
    #
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
    vx
    vy
    cA
    cB
    @6
    vw
    cv
    #
    cF
    cfv
    #
    clt
    wbr
    #
    vw
    cA
    crab
    #
    cxr
    clt
    csup
    #
    cmnf
    @19
    cioo
    co
    #
    @6
    cmnf
    @19
    cioc
    co
    #
    cF
    cJ
    @12
    vb
    wph
    @7
    vx
    decsmf.x
    @7
    vx
    nfv
    nfan
    wph
    @7
    vy
    decsmf.y
    @7
    vy
    nfv
    nfan
    wph
    cA
    cr
    wss
    @7
    decsmf.a
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
    decsmf.f
    frexr
    adantr
    @8
    @15
    vz
    cv
    #
    cle
    wbr
    #
    @22
    cF
    cfv
    #
    @16
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
    @9
    vy
    cv
    #
    cle
    wbr
    #
    @28
    cF
    cfv
    #
    @10
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
    #
    wph
    @27
    @7
    wph
    @33
    @27
    decsmf.i
    @32
    @26
    @15
    @28
    cle
    wbr
    #
    @30
    @16
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
    @15
    wceq
    #
    @29
    @34
    @31
    @35
    @9
    @15
    @28
    cle
    breq1
    @36
    @10
    @16
    @30
    cle
    @9
    @15
    cF
    fveq2
    breq2d
    imbi12d
    @28
    @22
    wceq
    #
    @34
    @23
    @35
    @25
    @28
    @22
    @15
    cle
    breq2
    @37
    @30
    @24
    @16
    cle
    @28
    @22
    cF
    fveq2
    breq1d
    imbi12d
    cbvral2v
    #
    sylib
    adantr
    @38
    sylibr
    decsmf.j
    decsmf.b
    @7
    @6
    cxr
    wcel
    wph
    @6
    rexr
    adantl
    @12
    eqid
    cxr
    @18
    @12
    clt
    @17
    @11
    vw
    vx
    cA
    @15
    @9
    wceq
    @16
    @10
    @6
    clt
    @15
    @9
    cF
    fveq2
    breq2d
    cbvrabv
    supeq1i
    @20
    eqid
    @21
    eqid
    decsmflem
    wph
    @13
    @14
    wb
    #
    @7
    wph
    cB
    cvv
    wcel
    cA
    cvv
    wcel
    @39
    wph
    cB
    csalg
    @2
    elexd
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
    decsmf.a
    ssexd
    vb
    @12
    cA
    cB
    cvv
    cvv
    elrest
    syl2anc
    adantr
    mpbird
    issmfgtd
end
