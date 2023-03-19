include "cv.mm"
include "wss.mm"
include "cat.mm"
include "crab.mm"
include "cuni.mm"
include "cspn.mm"
include "cfv.mm"
include "wcel.mm"
include "c0v.mm"
include "eleq1.mm"
include "wne.mm"
include "wa.mm"
include "csn.mm"
include "wceq.mm"
include "chil.mm"
include "csh.mm"
include "sheli.mm"
include "spansnsh.mm"
include "spanid.mm"
include "3syl.mm"
include "adantr.mm"
include "spansna.mm"
include "sylan.mm"
include "spansnss.mm"
include "mpan.mm"
include "sseq1.mm"
include "elrab.mm"
include "sylanbrc.mm"
include "elssuni.mm"
include "cch.mm"
include "atssch.mm"
include "chsssh.mm"
include "sstri.mm"
include "rabss2.mm"
include "uniss.mm"
include "mp2b.mm"
include "unimax.mm"
include "ax-mp.mm"
include "shssii.mm"
include "eqsstri.mm"
include "spanss.mm"
include "eqsstr3d.mm"
include "spansnid.mm"
include "syl.mm"
include "sseldd.mm"
include "spancl.mm"
include "sh0.mm"
include "a1i.mm"
include "pm2.61ne.mm"
include "ssriv.mm"
include "mp2an.mm"
include "fveq2i.mm"
include "eqtri.mm"
include "sseqtri.mm"
include "eqssi.mm"

theorem shatomistici
  let vx: setvar x
  let cA: class A
  let vy: setvar y
  assume shatomistic.1: |- A e. SH

  disjoint A x
  disjoint x y
  disjoint A y
  assert |- A = ( span ` U. { x e. HAtoms | x C_ A } )

  proof
    cA
    vx
    cv
    #
    cA
    wss
    #
    vx
    cat
    crab
    #
    cuni
    #
    cspn
    cfv
    #
    vy
    cA
    @4
    vy
    cv
    #
    cA
    wcel
    #
    @5
    @4
    wcel
    c0v
    @4
    wcel
    #
    @5
    c0v
    @5
    c0v
    @4
    eleq1
    @6
    @5
    c0v
    wne
    #
    wa
    #
    @5
    csn
    cspn
    cfv
    #
    @4
    @5
    @9
    @10
    @10
    cspn
    cfv
    #
    @4
    @6
    @11
    @10
    wceq
    #
    @8
    @6
    @5
    chil
    wcel
    #
    @10
    csh
    wcel
    @12
    @5
    cA
    shatomistic.1
    sheli
    #
    @5
    spansnsh
    @10
    spanid
    3syl
    adantr
    @9
    @10
    @2
    wcel
    #
    @10
    @3
    wss
    #
    @11
    @4
    wss
    #
    @9
    @10
    cat
    wcel
    #
    @10
    cA
    wss
    #
    @15
    @6
    @13
    @8
    @18
    @14
    @5
    spansna
    sylan
    @6
    @19
    @8
    cA
    csh
    wcel
    #
    @6
    @19
    shatomistic.1
    cA
    @5
    spansnss
    mpan
    adantr
    @1
    @19
    vx
    @10
    cat
    @0
    @10
    cA
    sseq1
    elrab
    sylanbrc
    @10
    @2
    elssuni
    @3
    chil
    wss
    #
    @16
    @17
    @3
    @1
    vx
    csh
    crab
    #
    cuni
    #
    chil
    cat
    csh
    wss
    @2
    @22
    wss
    @3
    @23
    wss
    #
    cat
    cch
    csh
    atssch
    chsssh
    sstri
    @1
    vx
    cat
    csh
    rabss2
    @2
    @22
    uniss
    mp2b
    #
    @23
    cA
    chil
    @20
    @23
    cA
    wceq
    shatomistic.1
    vx
    cA
    csh
    unimax
    ax-mp
    #
    cA
    shatomistic.1
    shssii
    eqsstri
    #
    sstri
    #
    @10
    @3
    spanss
    mpan
    3syl
    eqsstr3d
    @6
    @5
    @10
    wcel
    #
    @8
    @6
    @13
    @29
    @14
    @5
    spansnid
    syl
    adantr
    sseldd
    @7
    @6
    @21
    @4
    csh
    wcel
    @7
    @28
    @3
    spancl
    @4
    sh0
    mp2b
    a1i
    pm2.61ne
    ssriv
    @4
    @23
    cspn
    cfv
    #
    cA
    @23
    chil
    wss
    @24
    @4
    @30
    wss
    @27
    @25
    @3
    @23
    spanss
    mp2an
    @30
    cA
    cspn
    cfv
    #
    cA
    @23
    cA
    cspn
    @26
    fveq2i
    @20
    @31
    cA
    wceq
    shatomistic.1
    cA
    spanid
    ax-mp
    eqtri
    sseqtri
    eqssi
end
