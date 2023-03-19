include "wcel.mm"
include "cpw.mm"
include "cfin4.mm"
include "cfin3.mm"
include "com.mm"
include "cdom.mm"
include "wbr.mm"
include "wn.mm"
include "cv.mm"
include "wf1.mm"
include "wex.mm"
include "brdomi.mm"
include "wa.mm"
include "cvv.mm"
include "crn.mm"
include "cuni.mm"
include "wss.mm"
include "cfv.mm"
include "wpss.mm"
include "wi.mm"
include "wal.mm"
include "fin23lem33.mm"
include "adantl.mm"
include "crdg.mm"
include "cres.mm"
include "ssv.mm"
include "f1ss.mm"
include "mpan2.mm"
include "ad2antrr.mm"
include "wf.mm"
include "f1f.mm"
include "frn.mm"
include "uniss.mm"
include "3syl.mm"
include "unipw.mm"
include "syl6sseq.mm"
include "wceq.mm"
include "f1eq1.mm"
include "rneq.mm"
include "unieqd.mm"
include "sseq1d.mm"
include "anbi12d.mm"
include "wb.mm"
include "fveq2.mm"
include "syl.mm"
include "rneqd.mm"
include "psseq12d.mm"
include "imbi12d.mm"
include "cbvalv.mm"
include "biimpi.mm"
include "eqid.mm"
include "fin23lem39.mm"
include "exlimddv.mm"
include "pm2.01da.mm"
include "exlimiv.mm"
include "con2i.mm"
include "pwexg.mm"
include "isfin4-2.mm"
include "mpbird.mm"
include "isfin3.mm"
include "sylibr.mm"

theorem fin23lem41
  let vx: setvar x
  let cA: class A
  let vg: setvar g
  let cF: class F
  let va: setvar a
  let vb: setvar b
  let vc: setvar c
  let vd: setvar d
  let ve: setvar e
  let vf: setvar f
  assume fin23lem40.f: |- F = { g | A. a e. ( ~P g ^m _om ) ( A. x e. _om ( a ` suc x ) C_ ( a ` x ) -> |^| ran a e. ran a ) }

  disjoint a g
  disjoint a x
  disjoint A a
  disjoint g x
  disjoint A g
  disjoint A x
  disjoint F a
  disjoint a b
  disjoint a c
  disjoint a d
  disjoint a e
  disjoint a f
  disjoint b c
  disjoint b d
  disjoint b e
  disjoint b f
  disjoint b g
  disjoint b x
  disjoint A b
  disjoint c d
  disjoint c e
  disjoint c f
  disjoint c g
  disjoint c x
  disjoint A c
  disjoint d e
  disjoint d f
  disjoint d g
  disjoint d x
  disjoint A d
  disjoint e f
  disjoint e g
  disjoint e x
  disjoint A e
  disjoint f g
  disjoint f x
  disjoint A f
  disjoint F b
  disjoint F c
  disjoint F e
  assert |- ( A e. F -> A e. Fin3 )

  proof
    cA
    cF
    wcel
    #
    cA
    cpw
    #
    cfin4
    wcel
    #
    cA
    cfin3
    wcel
    @0
    @2
    com
    @1
    cdom
    wbr
    #
    wn
    #
    @3
    @0
    @3
    com
    @1
    vb
    cv
    #
    wf1
    #
    vb
    wex
    @0
    wn
    #
    com
    @1
    vb
    brdomi
    @6
    @7
    vb
    @6
    @0
    @6
    @0
    wa
    #
    com
    cvv
    vd
    cv
    #
    wf1
    #
    @9
    crn
    #
    cuni
    #
    cA
    wss
    #
    wa
    #
    com
    cvv
    @9
    vc
    cv
    #
    cfv
    #
    wf1
    #
    @16
    crn
    #
    cuni
    #
    @12
    wpss
    #
    wa
    #
    wi
    #
    vd
    wal
    #
    @7
    vc
    @0
    @23
    vc
    wex
    @6
    vx
    vc
    vg
    cF
    cA
    va
    vd
    fin23lem40.f
    fin23lem33
    adantl
    @8
    @23
    wa
    vx
    vg
    vb
    vc
    ve
    cF
    cA
    @15
    @5
    crdg
    com
    cres
    #
    va
    fin23lem40.f
    @6
    com
    cvv
    @5
    wf1
    #
    @0
    @23
    @6
    @1
    cvv
    wss
    @25
    @1
    ssv
    com
    @1
    cvv
    @5
    f1ss
    mpan2
    ad2antrr
    @6
    @5
    crn
    #
    cuni
    #
    cA
    wss
    @0
    @23
    @6
    @27
    @1
    cuni
    #
    cA
    @6
    com
    @1
    @5
    wf
    @26
    @1
    wss
    @27
    @28
    wss
    com
    @1
    @5
    f1f
    com
    @1
    @5
    frn
    @26
    @1
    uniss
    3syl
    cA
    unipw
    syl6sseq
    ad2antrr
    @23
    com
    cvv
    ve
    cv
    #
    wf1
    #
    @29
    crn
    #
    cuni
    #
    cA
    wss
    #
    wa
    #
    com
    cvv
    @29
    @15
    cfv
    #
    wf1
    #
    @35
    crn
    #
    cuni
    #
    @32
    wpss
    #
    wa
    #
    wi
    #
    ve
    wal
    #
    @8
    @23
    @42
    @22
    @41
    vd
    ve
    @9
    @29
    wceq
    #
    @14
    @34
    @21
    @40
    @43
    @10
    @30
    @13
    @33
    com
    cvv
    @9
    @29
    f1eq1
    @43
    @12
    @32
    cA
    @43
    @11
    @31
    @9
    @29
    rneq
    unieqd
    #
    sseq1d
    anbi12d
    @43
    @17
    @36
    @20
    @39
    @43
    @16
    @35
    wceq
    @17
    @36
    wb
    @9
    @29
    @15
    fveq2
    #
    com
    cvv
    @16
    @35
    f1eq1
    syl
    @43
    @19
    @38
    @12
    @32
    @43
    @18
    @37
    @43
    @16
    @35
    @45
    rneqd
    unieqd
    @44
    psseq12d
    anbi12d
    imbi12d
    cbvalv
    biimpi
    adantl
    @24
    eqid
    fin23lem39
    exlimddv
    pm2.01da
    exlimiv
    syl
    con2i
    @0
    @1
    cvv
    wcel
    @2
    @4
    wb
    cA
    cF
    pwexg
    @1
    cvv
    isfin4-2
    syl
    mpbird
    cA
    isfin3
    sylibr
end
