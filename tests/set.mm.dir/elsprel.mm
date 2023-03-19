include "wcel.mm"
include "wo.mm"
include "cpr.mm"
include "cv.mm"
include "wceq.mm"
include "wex.mm"
include "cab.mm"
include "cvv.mm"
include "elex.mm"
include "orim12i.mm"
include "wi.mm"
include "elisset.mm"
include "wa.mm"
include "eeanv.mm"
include "preq12.mm"
include "eqcomd.mm"
include "2eximi.mm"
include "sylbir.mm"
include "syl2an.mm"
include "expcom.mm"
include "wn.mm"
include "csn.mm"
include "preq2.mm"
include "adantr.mm"
include "dfsn2.mm"
include "sneq.mm"
include "adantl.mm"
include "syl5eqr.mm"
include "eqtr2d.mm"
include "ex.mm"
include "spimev.mm"
include "prprc2.mm"
include "eqeq1d.mm"
include "exbidv.mm"
include "mpbird.mm"
include "eximdv.mm"
include "syl5.mm"
include "pm2.61i.mm"
include "preq1.mm"
include "prprc1.mm"
include "impcom.mm"
include "excom.mm"
include "sylibr.mm"
include "syl11.mm"
include "jaoi.mm"
include "syl.mm"
include "prex.mm"
include "eqeq1.mm"
include "2exbidv.mm"
include "elab.mm"

theorem elsprel
  let cA: class A
  let cB: class B
  let cV: class V
  let cW: class W
  let vp: setvar p
  let va: setvar a
  let vb: setvar b
  let vk: setvar k
  let vx: setvar x

  disjoint A a
  disjoint A b
  disjoint A p
  disjoint a b
  disjoint a p
  disjoint b p
  disjoint B a
  disjoint B b
  disjoint B p
  disjoint k x
  assert |- ( ( A e. V \/ B e. W ) -> { A , B } e. { p | E. a E. b p = { a , b } } )

  proof
    cA
    cV
    wcel
    #
    cB
    cW
    wcel
    #
    wo
    #
    cA
    cB
    cpr
    #
    va
    cv
    #
    vb
    cv
    #
    cpr
    #
    wceq
    #
    vb
    wex
    #
    va
    wex
    #
    @3
    vp
    cv
    #
    @6
    wceq
    #
    vb
    wex
    va
    wex
    #
    vp
    cab
    wcel
    @2
    cA
    cvv
    wcel
    #
    cB
    cvv
    wcel
    #
    wo
    @9
    @0
    @13
    @1
    @14
    cA
    cV
    elex
    cB
    cW
    elex
    orim12i
    @13
    @9
    @14
    @14
    @13
    @9
    wi
    @13
    @14
    @9
    @13
    @4
    cA
    wceq
    #
    va
    wex
    #
    @5
    cB
    wceq
    #
    vb
    wex
    #
    @9
    @14
    va
    cA
    cvv
    elisset
    #
    vb
    cB
    cvv
    elisset
    #
    @16
    @18
    wa
    @15
    @17
    wa
    #
    vb
    wex
    va
    wex
    @9
    @15
    @17
    va
    vb
    eeanv
    @21
    @7
    va
    vb
    @21
    @6
    @3
    @4
    @5
    cA
    cB
    preq12
    eqcomd
    2eximi
    sylbir
    syl2an
    #
    expcom
    @13
    @16
    @14
    wn
    #
    @9
    @19
    @23
    @15
    @8
    va
    @23
    @15
    @8
    @23
    @15
    wa
    #
    @8
    cA
    csn
    #
    @6
    wceq
    #
    vb
    wex
    #
    @15
    @27
    @23
    @15
    @26
    vb
    va
    @5
    @4
    wceq
    #
    @15
    @26
    @28
    @15
    wa
    #
    @6
    @4
    @4
    cpr
    #
    @25
    @28
    @6
    @30
    wceq
    @15
    @5
    @4
    @4
    preq2
    adantr
    @29
    @30
    @4
    csn
    #
    @25
    @4
    dfsn2
    @15
    @31
    @25
    wceq
    @28
    @4
    cA
    sneq
    adantl
    syl5eqr
    eqtr2d
    ex
    spimev
    adantl
    @24
    @7
    @26
    vb
    @24
    @3
    @25
    @6
    @23
    @3
    @25
    wceq
    @15
    cA
    cB
    prprc2
    adantr
    eqeq1d
    exbidv
    mpbird
    ex
    eximdv
    syl5
    pm2.61i
    @13
    @14
    @9
    wi
    @13
    @14
    @9
    @22
    ex
    @18
    @13
    wn
    #
    @9
    @14
    @18
    @32
    @9
    @18
    @32
    wa
    @7
    va
    wex
    #
    vb
    wex
    #
    @9
    @32
    @18
    @34
    @32
    @17
    @33
    vb
    @32
    @17
    @33
    @32
    @17
    wa
    #
    @33
    cB
    csn
    #
    @6
    wceq
    #
    va
    wex
    #
    @17
    @38
    @32
    @17
    @37
    va
    vb
    @4
    @5
    wceq
    #
    @17
    @37
    @39
    @17
    wa
    #
    @6
    @5
    @5
    cpr
    #
    @36
    @39
    @6
    @41
    wceq
    @17
    @4
    @5
    @5
    preq1
    adantr
    @40
    @41
    @5
    csn
    #
    @36
    @5
    dfsn2
    @17
    @42
    @36
    wceq
    @39
    @5
    cB
    sneq
    adantl
    syl5eqr
    eqtr2d
    ex
    spimev
    adantl
    @35
    @7
    @37
    va
    @35
    @3
    @36
    @6
    @32
    @3
    @36
    wceq
    @17
    cA
    cB
    prprc1
    adantr
    eqeq1d
    exbidv
    mpbird
    ex
    eximdv
    impcom
    @7
    va
    vb
    excom
    sylibr
    ex
    @20
    syl11
    pm2.61i
    jaoi
    syl
    @12
    @9
    vp
    @3
    cA
    cB
    prex
    @10
    @3
    wceq
    @11
    @7
    va
    vb
    @10
    @3
    @6
    eqeq1
    2exbidv
    elab
    sylibr
end
