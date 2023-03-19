include "cc0.mm"
include "cv.mm"
include "cfv.mm"
include "cle.mm"
include "wbr.mm"
include "cc.mm"
include "cin.mm"
include "wral.mm"
include "c0p.mm"
include "cofr.mm"
include "csn.mm"
include "cxp.mm"
include "wss.mm"
include "wceq.mm"
include "sseqin2.mm"
include "sylib.mm"
include "raleqdv.mm"
include "cvv.mm"
include "wfn.mm"
include "wcel.mm"
include "0cn.mm"
include "fnconstg.mm"
include "ax-mp.mm"
include "df-0p.mm"
include "fneq1i.mm"
include "mpbir.mm"
include "a1i.mm"
include "cnex.mm"
include "ssexg.mm"
include "sylancl.mm"
include "eqid.mm"
include "0pval.mm"
include "adantl.mm"
include "wa.mm"
include "eqidd.mm"
include "ofrfval.mm"
include "inidm.mm"
include "c0ex.mm"
include "fvconst2.mm"
include "3bitr4d.mm"

theorem 0pledm
  let wph: wff ph
  let cA: class A
  let cF: class F
  let vx: setvar x
  assume 0pledm.1: |- ( ph -> A C_ CC )
  assume 0pledm.2: |- ( ph -> F Fn A )


  assert |- ( ph -> ( 0p oR <_ F <-> ( A X. { 0 } ) oR <_ F ) )

  proof
    wph
    cc0
    vx
    cv
    #
    cF
    cfv
    #
    cle
    wbr
    #
    vx
    cc
    cA
    cin
    #
    wral
    @2
    vx
    cA
    wral
    c0p
    cF
    cle
    cofr
    #
    wbr
    cA
    cc0
    csn
    #
    cxp
    #
    cF
    @4
    wbr
    wph
    @2
    vx
    @3
    cA
    wph
    cA
    cc
    wss
    #
    @3
    cA
    wceq
    0pledm.1
    cA
    cc
    sseqin2
    sylib
    raleqdv
    wph
    vx
    cc
    cA
    cc0
    @1
    cle
    @3
    c0p
    cF
    cvv
    cvv
    c0p
    cc
    wfn
    #
    wph
    @8
    cc
    @5
    cxp
    #
    cc
    wfn
    #
    cc0
    cc
    wcel
    #
    @10
    0cn
    cc
    cc0
    cc
    fnconstg
    ax-mp
    cc
    c0p
    @9
    df-0p
    fneq1i
    mpbir
    a1i
    0pledm.2
    cc
    cvv
    wcel
    #
    wph
    cnex
    a1i
    wph
    @7
    @12
    cA
    cvv
    wcel
    0pledm.1
    cnex
    cA
    cc
    cvv
    ssexg
    sylancl
    #
    @3
    eqid
    @0
    cc
    wcel
    @0
    c0p
    cfv
    cc0
    wceq
    wph
    @0
    0pval
    adantl
    wph
    @0
    cA
    wcel
    #
    wa
    @1
    eqidd
    #
    ofrfval
    wph
    vx
    cA
    cA
    cc0
    @1
    cle
    cA
    @6
    cF
    cvv
    cvv
    @6
    cA
    wfn
    #
    wph
    @11
    @16
    0cn
    cA
    cc0
    cc
    fnconstg
    ax-mp
    a1i
    0pledm.2
    @13
    @13
    cA
    inidm
    @14
    @0
    @6
    cfv
    cc0
    wceq
    wph
    cA
    cc0
    @0
    c0ex
    fvconst2
    adantl
    @15
    ofrfval
    3bitr4d
end
