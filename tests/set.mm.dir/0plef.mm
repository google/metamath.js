include "cr.mm"
include "cc0.mm"
include "cpnf.mm"
include "cico.mm"
include "co.mm"
include "wf.mm"
include "c0p.mm"
include "cle.mm"
include "cofr.mm"
include "wbr.mm"
include "wss.mm"
include "rge0ssre.mm"
include "fss.mm"
include "mpan2.mm"
include "cv.mm"
include "cfv.mm"
include "wcel.mm"
include "wral.mm"
include "wa.mm"
include "wb.mm"
include "ffvelrn.mm"
include "elrege0.mm"
include "baib.mm"
include "syl.mm"
include "ralbidva.mm"
include "wfn.mm"
include "ffn.mm"
include "ffnfv.mm"
include "cc.mm"
include "cvv.mm"
include "csn.mm"
include "cxp.mm"
include "0cn.mm"
include "fnconstg.mm"
include "ax-mp.mm"
include "df-0p.mm"
include "fneq1i.mm"
include "mpbir.mm"
include "a1i.mm"
include "cnex.mm"
include "reex.mm"
include "cin.mm"
include "wceq.mm"
include "ax-resscn.mm"
include "sseqin2.mm"
include "mpbi.mm"
include "0pval.mm"
include "adantl.mm"
include "eqidd.mm"
include "ofrfval.mm"
include "3bitr4d.mm"
include "biadan2.mm"

theorem 0plef
  let cF: class F
  let cA: class A
  let vx: setvar x
  let wph: wff ph


  assert |- ( F : RR --> ( 0 [,) +oo ) <-> ( F : RR --> RR /\ 0p oR <_ F ) )

  proof
    cr
    cc0
    cpnf
    cico
    co
    #
    cF
    wf
    #
    cr
    cr
    cF
    wf
    #
    c0p
    cF
    cle
    cofr
    wbr
    #
    @1
    @0
    cr
    wss
    @2
    rge0ssre
    cr
    @0
    cr
    cF
    fss
    mpan2
    @2
    vx
    cv
    #
    cF
    cfv
    #
    @0
    wcel
    #
    vx
    cr
    wral
    #
    cc0
    @5
    cle
    wbr
    #
    vx
    cr
    wral
    @1
    @3
    @2
    @6
    @8
    vx
    cr
    @2
    @4
    cr
    wcel
    wa
    #
    @5
    cr
    wcel
    #
    @6
    @8
    wb
    cr
    cr
    @4
    cF
    ffvelrn
    @6
    @10
    @8
    @5
    elrege0
    baib
    syl
    ralbidva
    @2
    cF
    cr
    wfn
    #
    @1
    @7
    wb
    cr
    cr
    cF
    ffn
    #
    @1
    @11
    @7
    vx
    cr
    @0
    cF
    ffnfv
    baib
    syl
    @2
    vx
    cc
    cr
    cc0
    @5
    cle
    cr
    c0p
    cF
    cvv
    cvv
    c0p
    cc
    wfn
    #
    @2
    @13
    cc
    cc0
    csn
    cxp
    #
    cc
    wfn
    #
    cc0
    cc
    wcel
    @15
    0cn
    cc
    cc0
    cc
    fnconstg
    ax-mp
    cc
    c0p
    @14
    df-0p
    fneq1i
    mpbir
    a1i
    @12
    cc
    cvv
    wcel
    @2
    cnex
    a1i
    cr
    cvv
    wcel
    @2
    reex
    a1i
    cr
    cc
    wss
    cc
    cr
    cin
    cr
    wceq
    ax-resscn
    cr
    cc
    sseqin2
    mpbi
    @4
    cc
    wcel
    @4
    c0p
    cfv
    cc0
    wceq
    @2
    @4
    0pval
    adantl
    @9
    @5
    eqidd
    ofrfval
    3bitr4d
    biadan2
end
