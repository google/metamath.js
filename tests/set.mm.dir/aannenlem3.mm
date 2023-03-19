include "caa.mm"
include "cn.mm"
include "cdom.mm"
include "wbr.mm"
include "cen.mm"
include "com.mm"
include "cc.mm"
include "cv.mm"
include "wor.mm"
include "crn.mm"
include "cuni.mm"
include "aannenlem2.mm"
include "cfn.mm"
include "wss.mm"
include "cn0.mm"
include "ccrd.mm"
include "cdm.mm"
include "wcel.mm"
include "wfo.mm"
include "con0.mm"
include "omelon.mm"
include "nn0ennn.mm"
include "nnenom.mm"
include "entri.mm"
include "ensymi.mm"
include "isnumi.mm"
include "mp2an.mm"
include "wfn.mm"
include "cfv.mm"
include "cc0.mm"
include "wceq.mm"
include "c0p.mm"
include "wne.mm"
include "cdgr.mm"
include "cle.mm"
include "ccoe.mm"
include "cabs.mm"
include "wral.mm"
include "w3a.mm"
include "cz.mm"
include "cply.mm"
include "crab.mm"
include "wrex.mm"
include "cnex.mm"
include "rabex.mm"
include "fnmpti.mm"
include "dffn4.mm"
include "mpbi.mm"
include "fodomnum.mm"
include "mp2.mm"
include "domentr.mm"
include "a1i.mm"
include "wb.mm"
include "fvelrnb.mm"
include "ax-mp.mm"
include "aannenlem1.mm"
include "eleq1.mm"
include "syl5ibcom.mm"
include "rexlimiv.mm"
include "sylbi.mm"
include "ssriv.mm"
include "wi.mm"
include "aasscn.mm"
include "eqsstr3i.mm"
include "soss.mm"
include "iunfictbso.mm"
include "syl3anc.mm"
include "syl5eqbr.mm"
include "cnso.mm"
include "exlimiiv.mm"
include "cvv.mm"
include "ssexi.mm"
include "cq.mm"
include "nnssq.mm"
include "qssaa.mm"
include "sstri.mm"
include "ssdomg.mm"
include "sbth.mm"

theorem aannenlem3
  let ve: setvar e
  let cH: class H
  let va: setvar a
  let vb: setvar b
  let vc: setvar c
  let vd: setvar d
  let cA: class A
  let vf: setvar f
  let vg: setvar g
  let vh: setvar h
  let vi: setvar i
  assume aannenlem.a: |- H = ( a e. NN0 |-> { b e. CC | E. c e. { d e. ( Poly ` ZZ ) | ( d =/= 0p /\ ( deg ` d ) <_ a /\ A. e e. NN0 ( abs ` ( ( coeff ` d ) ` e ) ) <_ a ) } ( c ` b ) = 0 } )

  disjoint a b
  disjoint a c
  disjoint a d
  disjoint a e
  disjoint b c
  disjoint b d
  disjoint b e
  disjoint c d
  disjoint c e
  disjoint d e
  disjoint A a
  disjoint A b
  disjoint A c
  disjoint A d
  disjoint A e
  disjoint A f
  disjoint A g
  disjoint A h
  disjoint A i
  disjoint a f
  disjoint a g
  disjoint a h
  disjoint a i
  disjoint b f
  disjoint b g
  disjoint b h
  disjoint b i
  disjoint c f
  disjoint c g
  disjoint c h
  disjoint c i
  disjoint d f
  disjoint d g
  disjoint d h
  disjoint d i
  disjoint e f
  disjoint e g
  disjoint e h
  disjoint e i
  disjoint f g
  disjoint f h
  disjoint f i
  disjoint g h
  disjoint g i
  disjoint h i
  disjoint H f
  disjoint H g
  assert |- AA ~~ NN

  proof
    caa
    cn
    cdom
    wbr
    #
    cn
    caa
    cdom
    wbr
    #
    caa
    cn
    cen
    wbr
    caa
    com
    cdom
    wbr
    #
    com
    cn
    cen
    wbr
    @0
    cc
    vf
    cv
    #
    wor
    #
    @2
    vf
    @4
    caa
    cH
    crn
    #
    cuni
    #
    com
    cdom
    ve
    cH
    va
    vb
    vc
    vd
    aannenlem.a
    aannenlem2
    #
    @4
    @5
    com
    cdom
    wbr
    #
    @5
    cfn
    wss
    #
    @6
    @3
    wor
    #
    @6
    com
    cdom
    wbr
    @8
    @4
    @5
    cn0
    cdom
    wbr
    #
    cn0
    com
    cen
    wbr
    @8
    cn0
    ccrd
    cdm
    wcel
    #
    cn0
    @5
    cH
    wfo
    #
    @11
    com
    con0
    wcel
    com
    cn0
    cen
    wbr
    @12
    omelon
    cn0
    com
    cn0
    cn
    com
    nn0ennn
    nnenom
    entri
    #
    ensymi
    com
    cn0
    isnumi
    mp2an
    cH
    cn0
    wfn
    #
    @13
    va
    cn0
    vb
    cv
    vc
    cv
    cfv
    cc0
    wceq
    vc
    vd
    cv
    #
    c0p
    wne
    @16
    cdgr
    cfv
    va
    cv
    #
    cle
    wbr
    ve
    cv
    @16
    ccoe
    cfv
    cfv
    cabs
    cfv
    @17
    cle
    wbr
    ve
    cn0
    wral
    w3a
    vd
    cz
    cply
    cfv
    crab
    wrex
    #
    vb
    cc
    crab
    cH
    @18
    vb
    cc
    cnex
    rabex
    aannenlem.a
    fnmpti
    #
    cn0
    cH
    dffn4
    mpbi
    cn0
    @5
    cH
    fodomnum
    mp2
    @14
    @5
    cn0
    com
    domentr
    mp2an
    a1i
    @9
    @4
    vf
    @5
    cfn
    @3
    @5
    wcel
    #
    vg
    cv
    #
    cH
    cfv
    #
    @3
    wceq
    #
    vg
    cn0
    wrex
    #
    @3
    cfn
    wcel
    #
    @15
    @20
    @24
    wb
    @19
    vg
    cn0
    @3
    cH
    fvelrnb
    ax-mp
    @23
    @25
    vg
    cn0
    @21
    cn0
    wcel
    @22
    cfn
    wcel
    @23
    @25
    @21
    ve
    cH
    va
    vb
    vc
    vd
    aannenlem.a
    aannenlem1
    @22
    @3
    cfn
    eleq1
    syl5ibcom
    rexlimiv
    sylbi
    ssriv
    a1i
    @6
    cc
    wss
    @4
    @10
    wi
    @6
    caa
    cc
    @7
    aasscn
    eqsstr3i
    @6
    cc
    @3
    soss
    ax-mp
    @5
    @3
    iunfictbso
    syl3anc
    syl5eqbr
    vf
    cnso
    exlimiiv
    cn
    com
    nnenom
    ensymi
    caa
    com
    cn
    domentr
    mp2an
    caa
    cvv
    wcel
    cn
    caa
    wss
    @1
    caa
    cc
    cnex
    aasscn
    ssexi
    cn
    cq
    caa
    nnssq
    qssaa
    sstri
    cn
    caa
    cvv
    ssdomg
    mp2
    caa
    cn
    sbth
    mp2an
end
