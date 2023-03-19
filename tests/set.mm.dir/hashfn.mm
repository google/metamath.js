include "wfn.mm"
include "cvv.mm"
include "wcel.mm"
include "chash.mm"
include "cfv.mm"
include "wceq.mm"
include "wa.mm"
include "cen.mm"
include "wbr.mm"
include "fndmeng.mm"
include "ensym.mm"
include "hasheni.mm"
include "3syl.mm"
include "wn.mm"
include "c0.mm"
include "cdm.mm"
include "dmexg.mm"
include "fndm.mm"
include "eleq1d.mm"
include "syl5ib.mm"
include "con3dimp.mm"
include "fvprc.mm"
include "syl.mm"
include "adantl.mm"
include "eqtr4d.mm"
include "pm2.61dan.mm"

theorem hashfn
  let cA: class A
  let cF: class F


  assert |- ( F Fn A -> ( # ` F ) = ( # ` A ) )

  proof
    cF
    cA
    wfn
    #
    cA
    cvv
    wcel
    #
    cF
    chash
    cfv
    #
    cA
    chash
    cfv
    #
    wceq
    #
    @0
    @1
    wa
    cA
    cF
    cen
    wbr
    cF
    cA
    cen
    wbr
    @4
    cA
    cvv
    cF
    fndmeng
    cA
    cF
    ensym
    cF
    cA
    hasheni
    3syl
    @0
    @1
    wn
    #
    wa
    #
    @2
    c0
    @3
    @6
    cF
    cvv
    wcel
    #
    wn
    @2
    c0
    wceq
    @0
    @7
    @1
    @7
    cF
    cdm
    #
    cvv
    wcel
    @0
    @1
    cF
    cvv
    dmexg
    @0
    @8
    cA
    cvv
    cA
    cF
    fndm
    eleq1d
    syl5ib
    con3dimp
    cF
    chash
    fvprc
    syl
    @5
    @3
    c0
    wceq
    @0
    cA
    chash
    fvprc
    adantl
    eqtr4d
    pm2.61dan
end
