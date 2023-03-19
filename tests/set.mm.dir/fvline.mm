include "cn.mm"
include "wcel.mm"
include "cee.mm"
include "cfv.mm"
include "wne.mm"
include "w3a.mm"
include "wa.mm"
include "cline2.mm"
include "co.mm"
include "cop.mm"
include "ccolin.mm"
include "ccnv.mm"
include "cec.mm"
include "cv.mm"
include "wbr.mm"
include "cab.mm"
include "wceq.mm"
include "wrex.mm"
include "coprab.mm"
include "eqid.mm"
include "fveq2.mm"
include "eleq2d.mm"
include "3anbi12d.mm"
include "anbi1d.mm"
include "rspcev.mm"
include "mpanr2.mm"
include "wb.mm"
include "simpr1.mm"
include "simpr2.mm"
include "cvv.mm"
include "colinearex.mm"
include "cnvex.mm"
include "ecexg.mm"
include "ax-mp.mm"
include "eleq1.mm"
include "neeq1.mm"
include "3anbi13d.mm"
include "opeq1.mm"
include "eceq1d.mm"
include "eqeq2d.mm"
include "anbi12d.mm"
include "rexbidv.mm"
include "neeq2.mm"
include "3anbi23d.mm"
include "opeq2.mm"
include "eqeq1.mm"
include "anbi2d.mm"
include "eloprabg.mm"
include "mp3an3.mm"
include "syl2anc.mm"
include "mpbird.mm"
include "df-ov.mm"
include "df-br.mm"
include "df-line2.mm"
include "eleq2i.mm"
include "bitri.mm"
include "wfun.mm"
include "wi.mm"
include "funline.mm"
include "funbrfv.mm"
include "sylbir.mm"
include "syl5eq.mm"
include "syl.mm"
include "opex.mm"
include "dfec2.mm"
include "vex.mm"
include "brcnv.mm"
include "abbii.mm"
include "eqtri.mm"
include "syl6eq.mm"

theorem fvline
  let vx: setvar x
  let cA: class A
  let cB: class B
  let cN: class N
  let va: setvar a
  let vb: setvar b
  let vl: setvar l
  let vn: setvar n

  disjoint A x
  disjoint B x
  disjoint A a
  disjoint a b
  disjoint A b
  disjoint a l
  disjoint A l
  disjoint a n
  disjoint A n
  disjoint B a
  disjoint B b
  disjoint b l
  disjoint B l
  disjoint b n
  disjoint B n
  disjoint l n
  disjoint N n
  assert |- ( ( N e. NN /\ ( A e. ( EE ` N ) /\ B e. ( EE ` N ) /\ A =/= B ) ) -> ( A Line B ) = { x | x Colinear <. A , B >. } )

  proof
    cN
    cn
    wcel
    #
    cA
    cN
    cee
    cfv
    #
    wcel
    #
    cB
    @1
    wcel
    #
    cA
    cB
    wne
    #
    w3a
    #
    wa
    #
    cA
    cB
    cline2
    co
    #
    cA
    cB
    cop
    #
    ccolin
    ccnv
    #
    cec
    #
    vx
    cv
    #
    @8
    ccolin
    wbr
    #
    vx
    cab
    #
    @6
    @8
    @10
    cop
    #
    va
    cv
    #
    vn
    cv
    #
    cee
    cfv
    #
    wcel
    #
    vb
    cv
    #
    @17
    wcel
    #
    @15
    @19
    wne
    #
    w3a
    #
    vl
    cv
    #
    @15
    @19
    cop
    #
    @9
    cec
    #
    wceq
    #
    wa
    #
    vn
    cn
    wrex
    #
    va
    vb
    vl
    coprab
    #
    wcel
    #
    @7
    @10
    wceq
    @6
    @30
    cA
    @17
    wcel
    #
    cB
    @17
    wcel
    #
    @4
    w3a
    #
    @10
    @10
    wceq
    #
    wa
    #
    vn
    cn
    wrex
    #
    @0
    @5
    @34
    @36
    @10
    eqid
    @35
    @5
    @34
    wa
    vn
    cN
    cn
    @16
    cN
    wceq
    #
    @33
    @5
    @34
    @37
    @31
    @2
    @32
    @3
    @4
    @37
    @17
    @1
    cA
    @16
    cN
    cee
    fveq2
    #
    eleq2d
    @37
    @17
    @1
    cB
    @38
    eleq2d
    3anbi12d
    anbi1d
    rspcev
    mpanr2
    @6
    @2
    @3
    @30
    @36
    wb
    #
    @0
    @2
    @3
    @4
    simpr1
    @0
    @2
    @3
    @4
    simpr2
    @2
    @3
    @10
    cvv
    wcel
    #
    @39
    @9
    cvv
    wcel
    @40
    ccolin
    colinearex
    cnvex
    @8
    cvv
    @9
    ecexg
    ax-mp
    @28
    @31
    @20
    cA
    @19
    wne
    #
    w3a
    #
    @23
    cA
    @19
    cop
    #
    @9
    cec
    #
    wceq
    #
    wa
    #
    vn
    cn
    wrex
    @33
    @23
    @10
    wceq
    #
    wa
    #
    vn
    cn
    wrex
    @36
    va
    vb
    vl
    cA
    cB
    @10
    @1
    @1
    cvv
    @15
    cA
    wceq
    #
    @27
    @46
    vn
    cn
    @49
    @22
    @42
    @26
    @45
    @49
    @18
    @31
    @21
    @41
    @20
    @15
    cA
    @17
    eleq1
    @15
    cA
    @19
    neeq1
    3anbi13d
    @49
    @25
    @44
    @23
    @49
    @24
    @43
    @9
    @15
    cA
    @19
    opeq1
    eceq1d
    eqeq2d
    anbi12d
    rexbidv
    @19
    cB
    wceq
    #
    @46
    @48
    vn
    cn
    @50
    @42
    @33
    @45
    @47
    @50
    @20
    @32
    @41
    @4
    @31
    @19
    cB
    @17
    eleq1
    @19
    cB
    cA
    neeq2
    3anbi23d
    @50
    @44
    @10
    @23
    @50
    @43
    @8
    @9
    @19
    cB
    cA
    opeq2
    eceq1d
    eqeq2d
    anbi12d
    rexbidv
    @47
    @48
    @35
    vn
    cn
    @47
    @47
    @34
    @33
    @23
    @10
    @10
    eqeq1
    anbi2d
    rexbidv
    eloprabg
    mp3an3
    syl2anc
    mpbird
    @30
    @7
    @8
    cline2
    cfv
    #
    @10
    cA
    cB
    cline2
    df-ov
    @30
    @8
    @10
    cline2
    wbr
    #
    @51
    @10
    wceq
    #
    @52
    @14
    cline2
    wcel
    @30
    @8
    @10
    cline2
    df-br
    cline2
    @29
    @14
    vn
    va
    vb
    vl
    df-line2
    eleq2i
    bitri
    cline2
    wfun
    @52
    @53
    wi
    funline
    @8
    @10
    cline2
    funbrfv
    ax-mp
    sylbir
    syl5eq
    syl
    @10
    @8
    @11
    @9
    wbr
    #
    vx
    cab
    #
    @13
    @8
    cvv
    wcel
    @10
    @55
    wceq
    cA
    cB
    opex
    #
    vx
    @8
    @9
    cvv
    dfec2
    ax-mp
    @54
    @12
    vx
    @8
    @11
    ccolin
    @56
    vx
    vex
    brcnv
    abbii
    eqtri
    syl6eq
end
