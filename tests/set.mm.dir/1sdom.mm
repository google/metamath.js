include "c1o.mm"
include "cv.mm"
include "csdm.mm"
include "wbr.mm"
include "weq.mm"
include "wn.mm"
include "wrex.mm"
include "breq2.mm"
include "rexeq.mm"
include "rexeqbi1dv.mm"
include "csuc.mm"
include "cdom.mm"
include "c2o.mm"
include "com.mm"
include "wcel.mm"
include "wb.mm"
include "1onn.mm"
include "sucdom.mm"
include "ax-mp.mm"
include "df-2o.mm"
include "breq1i.mm"
include "2dom.mm"
include "c0.mm"
include "cpr.mm"
include "df2o3.mm"
include "wel.mm"
include "wa.mm"
include "wf1.mm"
include "wex.mm"
include "cop.mm"
include "wss.mm"
include "wne.mm"
include "wfun.mm"
include "vex.mm"
include "0ex.mm"
include "elexi.mm"
include "funpr.mm"
include "df-ne.mm"
include "ccnv.mm"
include "wf.mm"
include "1n0.mm"
include "necomi.mm"
include "fpr.mm"
include "df-f1.mm"
include "mpbiran.mm"
include "csn.mm"
include "cun.mm"
include "cnvsn.mm"
include "uneq12i.mm"
include "df-pr.mm"
include "cnveqi.mm"
include "cnvun.mm"
include "eqtri.mm"
include "3eqtr4i.mm"
include "funeqi.mm"
include "bitr2i.mm"
include "3imtr3i.mm"
include "prssi.mm"
include "f1ss.mm"
include "syl2an.mm"
include "prex.mm"
include "f1eq1.mm"
include "spcev.mm"
include "syl.mm"
include "brdom.mm"
include "sylibr.mm"
include "expcom.mm"
include "rexlimivv.mm"
include "syl5eqbr.mm"
include "impbii.mm"
include "3bitr2i.mm"
include "vtoclbg.mm"

theorem 1sdom
  let vx: setvar x
  let vy: setvar y
  let cA: class A
  let cV: class V
  let va: setvar a
  let vf: setvar f

  disjoint x y
  disjoint A x
  disjoint A y
  disjoint a f
  disjoint a x
  disjoint a y
  disjoint A a
  disjoint f x
  disjoint f y
  disjoint A f
  assert |- ( A e. V -> ( 1o ~< A <-> E. x e. A E. y e. A -. x = y ) )

  proof
    c1o
    va
    cv
    #
    csdm
    wbr
    #
    vx
    vy
    weq
    wn
    #
    vy
    @0
    wrex
    #
    vx
    @0
    wrex
    #
    c1o
    cA
    csdm
    wbr
    @2
    vy
    cA
    wrex
    #
    vx
    cA
    wrex
    va
    cA
    cV
    @0
    cA
    c1o
    csdm
    breq2
    @3
    @5
    vx
    @0
    cA
    @2
    vy
    @0
    cA
    rexeq
    rexeqbi1dv
    @1
    c1o
    csuc
    #
    @0
    cdom
    wbr
    #
    c2o
    @0
    cdom
    wbr
    #
    @4
    c1o
    com
    wcel
    @1
    @7
    wb
    1onn
    c1o
    @0
    sucdom
    ax-mp
    c2o
    @6
    @0
    cdom
    df-2o
    breq1i
    @8
    @4
    vx
    vy
    @0
    2dom
    @4
    c2o
    c0
    c1o
    cpr
    #
    @0
    cdom
    df2o3
    @2
    @9
    @0
    cdom
    wbr
    #
    vx
    vy
    @0
    @0
    @2
    vx
    va
    wel
    vy
    va
    wel
    wa
    #
    @10
    @2
    @11
    wa
    #
    @9
    @0
    vf
    cv
    #
    wf1
    #
    vf
    wex
    #
    @10
    @12
    @9
    @0
    c0
    vx
    cv
    #
    cop
    #
    c1o
    vy
    cv
    #
    cop
    #
    cpr
    #
    wf1
    #
    @15
    @2
    @9
    @16
    @18
    cpr
    #
    @20
    wf1
    #
    @22
    @0
    wss
    @21
    @11
    @16
    @18
    wne
    @16
    c0
    cop
    #
    @18
    c1o
    cop
    #
    cpr
    #
    wfun
    #
    @2
    @23
    @16
    @18
    c0
    c1o
    vx
    vex
    #
    vy
    vex
    #
    0ex
    c1o
    com
    1onn
    elexi
    #
    funpr
    @16
    @18
    df-ne
    @23
    @20
    ccnv
    #
    wfun
    #
    @27
    @23
    @9
    @22
    @20
    wf
    #
    @32
    c0
    c1o
    wne
    @33
    c1o
    c0
    1n0
    necomi
    c0
    c1o
    @16
    @18
    0ex
    @30
    @28
    @29
    fpr
    ax-mp
    @9
    @22
    @20
    df-f1
    mpbiran
    @31
    @26
    @17
    csn
    #
    ccnv
    #
    @19
    csn
    #
    ccnv
    #
    cun
    #
    @24
    csn
    #
    @25
    csn
    #
    cun
    @31
    @26
    @35
    @39
    @37
    @40
    c0
    @16
    0ex
    @28
    cnvsn
    c1o
    @18
    @30
    @29
    cnvsn
    uneq12i
    @31
    @34
    @36
    cun
    #
    ccnv
    @38
    @20
    @41
    @17
    @19
    df-pr
    cnveqi
    @34
    @36
    cnvun
    eqtri
    @24
    @25
    df-pr
    3eqtr4i
    funeqi
    bitr2i
    3imtr3i
    @16
    @18
    @0
    prssi
    @9
    @22
    @0
    @20
    f1ss
    syl2an
    @14
    @21
    vf
    @20
    @17
    @19
    prex
    @9
    @0
    @13
    @20
    f1eq1
    spcev
    syl
    @9
    @0
    vf
    va
    vex
    brdom
    sylibr
    expcom
    rexlimivv
    syl5eqbr
    impbii
    3bitr2i
    vtoclbg
end
