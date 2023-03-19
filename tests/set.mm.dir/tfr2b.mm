include "word.mm"
include "con0.mm"
include "wcel.mm"
include "wceq.mm"
include "wo.mm"
include "cdm.mm"
include "cres.mm"
include "cvv.mm"
include "wb.mm"
include "ordeleqon.mm"
include "crecs.mm"
include "cv.mm"
include "wfn.mm"
include "cfv.mm"
include "wral.mm"
include "wa.mm"
include "wrex.mm"
include "cab.mm"
include "eqid.mm"
include "tfrlem15.mm"
include "dmeqi.mm"
include "eleq2i.mm"
include "reseq1i.mm"
include "eleq1i.mm"
include "3bitr4g.mm"
include "onprc.mm"
include "elex.mm"
include "mto.mm"
include "eleq1.mm"
include "mtbiri.mm"
include "tfrlem13.mm"
include "mtbir.mm"
include "reseq2.mm"
include "wrel.mm"
include "wss.mm"
include "wfun.mm"
include "wlim.mm"
include "tfr1a.mm"
include "simpli.mm"
include "funrel.mm"
include "ax-mp.mm"
include "simpri.mm"
include "limord.mm"
include "ordsson.mm"
include "mp2b.mm"
include "relssres.mm"
include "mp2an.mm"
include "syl6eq.mm"
include "eleq1d.mm"
include "2falsed.mm"
include "jaoi.mm"
include "sylbi.mm"

theorem tfr2b
  let cA: class A
  let cF: class F
  let cG: class G
  let vf: setvar f
  let vx: setvar x
  let vy: setvar y
  let cB: class B
  assume tfr.1: |- F = recs ( G )


  assert |- ( Ord A -> ( A e. dom F <-> ( F |` A ) e. _V ) )

  proof
    cA
    word
    cA
    con0
    wcel
    #
    cA
    con0
    wceq
    #
    wo
    cA
    cF
    cdm
    #
    wcel
    #
    cF
    cA
    cres
    #
    cvv
    wcel
    #
    wb
    #
    cA
    ordeleqon
    @0
    @6
    @1
    @0
    cA
    cG
    crecs
    #
    cdm
    #
    wcel
    @7
    cA
    cres
    #
    cvv
    wcel
    @3
    @5
    vx
    vy
    vf
    cv
    #
    vx
    cv
    #
    wfn
    vy
    cv
    #
    @10
    cfv
    @10
    @12
    cres
    cG
    cfv
    wceq
    vy
    @11
    wral
    wa
    vx
    con0
    wrex
    vf
    cab
    #
    cA
    vf
    cG
    @13
    eqid
    #
    tfrlem15
    @2
    @8
    cA
    cF
    @7
    tfr.1
    dmeqi
    eleq2i
    @4
    @9
    cvv
    cF
    @7
    cA
    tfr.1
    reseq1i
    eleq1i
    3bitr4g
    @1
    @3
    @5
    @1
    @3
    con0
    @2
    wcel
    #
    @15
    con0
    cvv
    wcel
    onprc
    con0
    @2
    elex
    mto
    cA
    con0
    @2
    eleq1
    mtbiri
    @1
    @5
    cF
    cvv
    wcel
    #
    @16
    @7
    cvv
    wcel
    vx
    vy
    @13
    vf
    cG
    @14
    tfrlem13
    cF
    @7
    cvv
    tfr.1
    eleq1i
    mtbir
    @1
    @4
    cF
    cvv
    @1
    @4
    cF
    con0
    cres
    #
    cF
    cA
    con0
    cF
    reseq2
    cF
    wrel
    #
    @2
    con0
    wss
    #
    @17
    cF
    wceq
    cF
    wfun
    #
    @18
    @20
    @2
    wlim
    #
    cF
    cG
    tfr.1
    tfr1a
    #
    simpli
    cF
    funrel
    ax-mp
    @21
    @2
    word
    @19
    @20
    @21
    @22
    simpri
    @2
    limord
    @2
    ordsson
    mp2b
    cF
    con0
    relssres
    mp2an
    syl6eq
    eleq1d
    mtbiri
    2falsed
    jaoi
    sylbi
end
