include "chil.mm"
include "wf.mm"
include "cr.mm"
include "wcel.mm"
include "cc0.mm"
include "cle.mm"
include "wbr.mm"
include "wa.mm"
include "cv.mm"
include "cfv.mm"
include "cno.mm"
include "cmul.mm"
include "co.mm"
include "wral.mm"
include "cnop.mm"
include "c1.mm"
include "wi.mm"
include "normcl.mm"
include "ad2antlr.mm"
include "simpllr.mm"
include "simpr.mm"
include "1re.mm"
include "lemul2a.mm"
include "mp3anl2.mm"
include "syl21anc.mm"
include "wceq.mm"
include "ax-1rid.mm"
include "ad2antrl.mm"
include "ad2antrr.mm"
include "breqtrd.mm"
include "ffvelrn.mm"
include "syl.mm"
include "adantlr.mm"
include "remulcl.mm"
include "sylan2.mm"
include "adantll.mm"
include "simplrl.mm"
include "letr.mm"
include "syl3anc.mm"
include "adantr.mm"
include "mpan2d.mm"
include "ex.mm"
include "com23.mm"
include "ralimdva.mm"
include "imp.mm"
include "cxr.mm"
include "wb.mm"
include "rexr.mm"
include "nmopub.mm"
include "biimpar.mm"
include "syldan.mm"
include "3impa.mm"

theorem nmopub2tALT
  let vx: setvar x
  let cA: class A
  let cT: class T
  let vw: setvar w
  let vy: setvar y
  let vz: setvar z
  let cB: class B
  let cC: class C
  let cS: class S

  disjoint A x
  disjoint T x
  disjoint w x
  disjoint w y
  disjoint w z
  disjoint A w
  disjoint x y
  disjoint x z
  disjoint y z
  disjoint A y
  disjoint A z
  disjoint B w
  disjoint B x
  disjoint B y
  disjoint B z
  disjoint C x
  disjoint C y
  disjoint C z
  disjoint S w
  disjoint S x
  disjoint S y
  disjoint S z
  disjoint T y
  disjoint T z
  disjoint T w
  assert |- ( ( T : ~H --> ~H /\ ( A e. RR /\ 0 <_ A ) /\ A. x e. ~H ( normh ` ( T ` x ) ) <_ ( A x. ( normh ` x ) ) ) -> ( normop ` T ) <_ A )

  proof
    chil
    chil
    cT
    wf
    #
    cA
    cr
    wcel
    #
    cc0
    cA
    cle
    wbr
    #
    wa
    #
    vx
    cv
    #
    cT
    cfv
    #
    cno
    cfv
    #
    cA
    @4
    cno
    cfv
    #
    cmul
    co
    #
    cle
    wbr
    #
    vx
    chil
    wral
    #
    cT
    cnop
    cfv
    cA
    cle
    wbr
    #
    @0
    @3
    wa
    #
    @10
    @7
    c1
    cle
    wbr
    #
    @6
    cA
    cle
    wbr
    #
    wi
    #
    vx
    chil
    wral
    #
    @11
    @12
    @10
    @16
    @12
    @9
    @15
    vx
    chil
    @12
    @4
    chil
    wcel
    #
    wa
    #
    @13
    @9
    @14
    @18
    @13
    @9
    @14
    wi
    @18
    @13
    wa
    #
    @9
    @8
    cA
    cle
    wbr
    #
    @14
    @19
    @8
    cA
    c1
    cmul
    co
    #
    cA
    cle
    @19
    @7
    cr
    wcel
    #
    @3
    @13
    @8
    @21
    cle
    wbr
    #
    @17
    @22
    @12
    @13
    @4
    normcl
    #
    ad2antlr
    @0
    @3
    @17
    @13
    simpllr
    @18
    @13
    simpr
    @22
    c1
    cr
    wcel
    @3
    @13
    @23
    1re
    @7
    c1
    cA
    lemul2a
    mp3anl2
    syl21anc
    @12
    @21
    cA
    wceq
    #
    @17
    @13
    @1
    @25
    @0
    @2
    cA
    ax-1rid
    ad2antrl
    ad2antrr
    breqtrd
    @18
    @9
    @20
    wa
    @14
    wi
    #
    @13
    @18
    @6
    cr
    wcel
    #
    @8
    cr
    wcel
    #
    @1
    @26
    @0
    @17
    @27
    @3
    @0
    @17
    wa
    @5
    chil
    wcel
    @27
    chil
    chil
    @4
    cT
    ffvelrn
    @5
    normcl
    syl
    adantlr
    @3
    @17
    @28
    @0
    @1
    @17
    @28
    @2
    @17
    @1
    @22
    @28
    @24
    cA
    @7
    remulcl
    sylan2
    adantlr
    adantll
    @0
    @1
    @2
    @17
    simplrl
    @6
    @8
    cA
    letr
    syl3anc
    adantr
    mpan2d
    ex
    com23
    ralimdva
    imp
    @12
    @11
    @16
    @3
    @0
    cA
    cxr
    wcel
    #
    @11
    @16
    wb
    @1
    @29
    @2
    cA
    rexr
    adantr
    vx
    cA
    cT
    nmopub
    sylan2
    biimpar
    syldan
    3impa
end
