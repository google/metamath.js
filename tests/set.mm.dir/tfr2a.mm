include "cdm.mm"
include "wcel.mm"
include "crecs.mm"
include "cfv.mm"
include "cres.mm"
include "wceq.mm"
include "cv.mm"
include "wfn.mm"
include "wral.mm"
include "wa.mm"
include "con0.mm"
include "wrex.mm"
include "cab.mm"
include "eqid.mm"
include "tfrlem9.mm"
include "dmeqi.mm"
include "eleq2s.mm"
include "fveq1i.mm"
include "reseq1i.mm"
include "fveq2i.mm"
include "3eqtr4g.mm"

theorem tfr2a
  let cA: class A
  let cF: class F
  let cG: class G
  let vf: setvar f
  let vx: setvar x
  let vy: setvar y
  let cB: class B
  assume tfr.1: |- F = recs ( G )


  assert |- ( A e. dom F -> ( F ` A ) = ( G ` ( F |` A ) ) )

  proof
    cA
    cF
    cdm
    #
    wcel
    cA
    cG
    crecs
    #
    cfv
    #
    @1
    cA
    cres
    #
    cG
    cfv
    #
    cA
    cF
    cfv
    cF
    cA
    cres
    #
    cG
    cfv
    @2
    @4
    wceq
    cA
    @1
    cdm
    @0
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
    @6
    cfv
    @6
    @8
    cres
    cG
    cfv
    wceq
    vy
    @7
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
    @9
    eqid
    tfrlem9
    cF
    @1
    tfr.1
    dmeqi
    eleq2s
    cA
    cF
    @1
    tfr.1
    fveq1i
    @5
    @3
    cG
    cF
    @1
    cA
    tfr.1
    reseq1i
    fveq2i
    3eqtr4g
end
