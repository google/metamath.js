include "cnpi.mm"
include "cxp.mm"
include "cnq.mm"
include "cerq.mm"
include "wf.mm"
include "wfn.mm"
include "crn.mm"
include "wss.mm"
include "wfun.mm"
include "cdm.mm"
include "wceq.mm"
include "wrel.mm"
include "cv.mm"
include "wbr.mm"
include "wmo.mm"
include "wal.mm"
include "cvv.mm"
include "ceq.mm"
include "cin.mm"
include "df-erq.mm"
include "inss2.mm"
include "eqsstri.mm"
include "xpss.mm"
include "sstri.mm"
include "df-rel.mm"
include "mpbir.mm"
include "wcel.mm"
include "wa.mm"
include "wi.mm"
include "wreu.mm"
include "nqereu.mm"
include "weu.mm"
include "df-reu.mm"
include "eumo.mm"
include "sylbi.mm"
include "syl.mm"
include "moanimv.mm"
include "brel.mm"
include "simpld.mm"
include "simprd.mm"
include "wer.mm"
include "enqer.mm"
include "a1i.mm"
include "inss1.mm"
include "ssbri.mm"
include "ersym.mm"
include "jca32.mm"
include "moimi.mm"
include "ax-mp.mm"
include "ax-gen.mm"
include "dffun6.mm"
include "mpbir2an.mm"
include "dmss.mm"
include "c1q.mm"
include "c0.mm"
include "wne.mm"
include "1nq.mm"
include "ne0i.mm"
include "dmxp.mm"
include "mp2b.mm"
include "sseqtri.mm"
include "wex.mm"
include "wrex.mm"
include "reurex.mm"
include "simpll.mm"
include "simplr.mm"
include "simpr.mm"
include "w3a.mm"
include "breqi.mm"
include "brinxp2.mm"
include "bitri.mm"
include "syl3anbrc.mm"
include "ex.mm"
include "reximdva.mm"
include "rexex.mm"
include "syl56.mm"
include "mpd.mm"
include "vex.mm"
include "eldm.mm"
include "sylibr.mm"
include "ssriv.mm"
include "eqssi.mm"
include "df-fn.mm"
include "rnss.mm"
include "rnxpss.mm"
include "df-f.mm"

theorem nqerf
  let vx: setvar x
  let vy: setvar y


  assert |- /Q : ( N. X. N. ) --> Q.

  proof
    cnpi
    cnpi
    cxp
    #
    cnq
    cerq
    wf
    cerq
    @0
    wfn
    #
    cerq
    crn
    #
    cnq
    wss
    @1
    cerq
    wfun
    #
    cerq
    cdm
    #
    @0
    wceq
    @3
    cerq
    wrel
    #
    vx
    cv
    #
    vy
    cv
    #
    cerq
    wbr
    #
    vy
    wmo
    #
    vx
    wal
    @5
    cerq
    cvv
    cvv
    cxp
    #
    wss
    cerq
    @0
    cnq
    cxp
    #
    @10
    cerq
    ceq
    @11
    cin
    #
    @11
    df-erq
    ceq
    @11
    inss2
    eqsstri
    #
    @0
    cnq
    xpss
    sstri
    cerq
    df-rel
    mpbir
    @9
    vx
    @6
    @0
    wcel
    #
    @7
    cnq
    wcel
    #
    @7
    @6
    ceq
    wbr
    #
    wa
    #
    wa
    #
    vy
    wmo
    #
    @9
    @19
    @14
    @17
    vy
    wmo
    #
    wi
    @14
    @16
    vy
    cnq
    wreu
    #
    @20
    vy
    @6
    nqereu
    #
    @21
    @17
    vy
    weu
    @20
    @16
    vy
    cnq
    df-reu
    @17
    vy
    eumo
    sylbi
    syl
    @14
    @17
    vy
    moanimv
    mpbir
    @8
    @18
    vy
    @8
    @14
    @15
    @16
    @8
    @14
    @15
    @6
    @7
    @0
    cnq
    cerq
    @13
    brel
    #
    simpld
    @8
    @14
    @15
    @23
    simprd
    @8
    @6
    @7
    ceq
    @0
    @0
    ceq
    wer
    #
    @8
    enqer
    a1i
    cerq
    ceq
    @6
    @7
    cerq
    @12
    ceq
    df-erq
    ceq
    @11
    inss1
    eqsstri
    ssbri
    ersym
    jca32
    moimi
    ax-mp
    ax-gen
    vx
    vy
    cerq
    dffun6
    mpbir2an
    @4
    @0
    @4
    @11
    cdm
    #
    @0
    cerq
    @11
    wss
    #
    @4
    @25
    wss
    @13
    cerq
    @11
    dmss
    ax-mp
    c1q
    cnq
    wcel
    cnq
    c0
    wne
    @25
    @0
    wceq
    1nq
    cnq
    c1q
    ne0i
    @0
    cnq
    dmxp
    mp2b
    sseqtri
    vx
    @0
    @4
    @14
    @8
    vy
    wex
    #
    @6
    @4
    wcel
    @14
    @21
    @27
    @22
    @21
    @16
    vy
    cnq
    wrex
    @14
    @8
    vy
    cnq
    wrex
    @27
    @16
    vy
    cnq
    reurex
    @14
    @16
    @8
    vy
    cnq
    @14
    @15
    wa
    #
    @16
    @8
    @28
    @16
    wa
    #
    @14
    @15
    @6
    @7
    ceq
    wbr
    #
    @8
    @14
    @15
    @16
    simpll
    @14
    @15
    @16
    simplr
    @29
    @7
    @6
    ceq
    @0
    @24
    @29
    enqer
    a1i
    @28
    @16
    simpr
    ersym
    @8
    @6
    @7
    @12
    wbr
    @14
    @15
    @30
    w3a
    @6
    @7
    cerq
    @12
    df-erq
    breqi
    @6
    @7
    @0
    cnq
    ceq
    brinxp2
    bitri
    syl3anbrc
    ex
    reximdva
    @8
    vy
    cnq
    rexex
    syl56
    mpd
    vy
    @6
    cerq
    vx
    vex
    eldm
    sylibr
    ssriv
    eqssi
    cerq
    @0
    df-fn
    mpbir2an
    @2
    @11
    crn
    #
    cnq
    @26
    @2
    @31
    wss
    @13
    cerq
    @11
    rnss
    ax-mp
    @0
    cnq
    rnxpss
    sstri
    @0
    cnq
    cerq
    df-f
    mpbir2an
end
