include "cv.mm"
include "cdm.mm"
include "cr1.mm"
include "cfv.mm"
include "con0.mm"
include "cep.mm"
include "csuc.mm"
include "crnk.mm"
include "wceq.mm"
include "suceq.mm"
include "fveq2d.mm"
include "wcel.mm"
include "wa.mm"
include "crab.mm"
include "wss.mm"
include "wwe.mm"
include "cab.mm"
include "cima.mm"
include "cuni.mm"
include "wfun.mm"
include "wfn.mm"
include "r1fnon.mm"
include "fnfun.mm"
include "ax-mp.mm"
include "fndm.mm"
include "eqimss2i.mm"
include "pm3.2i.mm"
include "funfvima2.mm"
include "mpsyl.mm"
include "elssuni.mm"
include "syl.mm"
include "sselda.mm"
include "rankidb.mm"
include "eleq2d.mm"
include "syl5ibcom.mm"
include "expimpd.mm"
include "ss2abdv.mm"
include "df-rab.mm"
include "abid1.mm"
include "3sstr4g.mm"
include "adantr.mm"
include "wral.mm"
include "rankr1ai.mm"
include "adantl.mm"
include "wb.mm"
include "word.mm"
include "eloni.mm"
include "limsuc2.mm"
include "syl2anc.mm"
include "mpbid.mm"
include "weq.mm"
include "fveq2.mm"
include "weeq12d.mm"
include "cbvralv.mm"
include "sylib.mm"
include "rspcva.mm"
include "wess.mm"
include "sylc.mm"
include "wf.mm"
include "rankf.mm"
include "a1i.mm"
include "fssresd.mm"
include "epweon.mm"
include "fnwe2.mm"

theorem aomclem4
  let wph: wff ph
  let vz: setvar z
  let cF: class F
  let va: setvar a
  let vb: setvar b
  let vc: setvar c
  assume aomclem4.f: |- F = { <. a , b >. | ( ( rank ` a ) _E ( rank ` b ) \/ ( ( rank ` a ) = ( rank ` b ) /\ a ( z ` suc ( rank ` a ) ) b ) ) }
  assume aomclem4.on: |- ( ph -> dom z e. On )
  assume aomclem4.su: |- ( ph -> dom z = U. dom z )
  assume aomclem4.we: |- ( ph -> A. a e. dom z ( z ` a ) We ( R1 ` a ) )

  disjoint a z
  disjoint b z
  disjoint a b
  disjoint a ph
  disjoint b ph
  disjoint c z
  disjoint a c
  disjoint b c
  disjoint c ph
  assert |- ( ph -> F We ( R1 ` dom z ) )

  proof
    wph
    va
    vb
    vc
    vz
    cv
    #
    cdm
    #
    cr1
    cfv
    #
    con0
    cep
    vc
    cv
    #
    csuc
    #
    @0
    cfv
    cF
    va
    cv
    #
    crnk
    cfv
    #
    csuc
    #
    @0
    cfv
    #
    crnk
    @3
    @6
    wceq
    @4
    @7
    @0
    @3
    @6
    suceq
    fveq2d
    aomclem4.f
    wph
    @5
    @2
    wcel
    #
    wa
    #
    vb
    cv
    #
    crnk
    cfv
    #
    @6
    wceq
    #
    vb
    @2
    crab
    #
    @7
    cr1
    cfv
    #
    wss
    #
    @15
    @8
    wwe
    #
    @14
    @8
    wwe
    wph
    @16
    @9
    wph
    @11
    @2
    wcel
    #
    @13
    wa
    #
    vb
    cab
    @11
    @15
    wcel
    #
    vb
    cab
    @14
    @15
    wph
    @19
    @20
    vb
    wph
    @18
    @13
    @20
    wph
    @18
    wa
    #
    @11
    @12
    csuc
    #
    cr1
    cfv
    #
    wcel
    #
    @13
    @20
    @21
    @11
    cr1
    con0
    cima
    #
    cuni
    #
    wcel
    @24
    wph
    @2
    @26
    @11
    wph
    @2
    @25
    wcel
    #
    @2
    @26
    wss
    cr1
    wfun
    #
    con0
    cr1
    cdm
    #
    wss
    #
    wa
    wph
    @1
    con0
    wcel
    #
    @27
    @28
    @30
    cr1
    con0
    wfn
    #
    @28
    r1fnon
    con0
    cr1
    fnfun
    ax-mp
    @29
    con0
    @32
    @29
    con0
    wceq
    r1fnon
    con0
    cr1
    fndm
    ax-mp
    eqimss2i
    pm3.2i
    aomclem4.on
    con0
    @1
    cr1
    funfvima2
    mpsyl
    @2
    @25
    elssuni
    syl
    #
    sselda
    @11
    rankidb
    syl
    @13
    @23
    @15
    @11
    @13
    @22
    @7
    cr1
    @12
    @6
    suceq
    fveq2d
    eleq2d
    syl5ibcom
    expimpd
    ss2abdv
    @13
    vb
    @2
    df-rab
    vb
    @15
    abid1
    3sstr4g
    adantr
    @10
    @7
    @1
    wcel
    #
    @11
    cr1
    cfv
    #
    @11
    @0
    cfv
    #
    wwe
    #
    vb
    @1
    wral
    #
    @17
    @10
    @6
    @1
    wcel
    #
    @34
    @9
    @39
    wph
    @5
    @1
    rankr1ai
    adantl
    wph
    @39
    @34
    wb
    #
    @9
    wph
    @1
    word
    #
    @1
    @1
    cuni
    wceq
    @40
    wph
    @31
    @41
    aomclem4.on
    @1
    eloni
    syl
    aomclem4.su
    @1
    @6
    limsuc2
    syl2anc
    adantr
    mpbid
    wph
    @38
    @9
    wph
    @5
    cr1
    cfv
    #
    @5
    @0
    cfv
    #
    wwe
    #
    va
    @1
    wral
    @38
    aomclem4.we
    @44
    @37
    va
    vb
    @1
    va
    vb
    weq
    @42
    @35
    @43
    @36
    @5
    @11
    @0
    fveq2
    @5
    @11
    cr1
    fveq2
    weeq12d
    cbvralv
    sylib
    adantr
    @37
    @17
    vb
    @7
    @1
    @11
    @7
    wceq
    @35
    @15
    @36
    @8
    @11
    @7
    @0
    fveq2
    @11
    @7
    cr1
    fveq2
    weeq12d
    rspcva
    syl2anc
    @14
    @15
    @8
    wess
    sylc
    wph
    @26
    con0
    @2
    crnk
    @26
    con0
    crnk
    wf
    wph
    rankf
    a1i
    @33
    fssresd
    con0
    cep
    wwe
    wph
    epweon
    a1i
    fnwe2
end
