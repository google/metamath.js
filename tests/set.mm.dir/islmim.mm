include "clmim.mm"
include "co.mm"
include "wcel.mm"
include "clmod.mm"
include "cv.mm"
include "wf1o.mm"
include "clmhm.mm"
include "crab.mm"
include "w3a.mm"
include "wa.mm"
include "cbs.mm"
include "cfv.mm"
include "df-lmim.mm"
include "ovex.mm"
include "rabex.mm"
include "wceq.mm"
include "oveq12.mm"
include "wb.mm"
include "fveq2.mm"
include "syl6eqr.mm"
include "f1oeq23.mm"
include "syl2an.mm"
include "rabeqbidv.mm"
include "elovmpt2.mm"
include "df-3an.mm"
include "f1oeq1.mm"
include "elrab.mm"
include "anbi2i.mm"
include "lmhmlmod1.mm"
include "lmhmlmod2.mm"
include "jca.mm"
include "adantr.mm"
include "pm4.71ri.mm"
include "bitr4i.mm"
include "3bitri.mm"

theorem islmim
  let cB: class B
  let cC: class C
  let cR: class R
  let cS: class S
  let cF: class F
  let va: setvar a
  let vb: setvar b
  let vc: setvar c
  assume islmim.b: |- B = ( Base ` R )
  assume islmim.c: |- C = ( Base ` S )


  assert |- ( F e. ( R LMIso S ) <-> ( F e. ( R LMHom S ) /\ F : B -1-1-onto-> C ) )

  proof
    cF
    cR
    cS
    clmim
    co
    wcel
    cR
    clmod
    wcel
    #
    cS
    clmod
    wcel
    #
    cF
    cB
    cC
    vc
    cv
    #
    wf1o
    #
    vc
    cR
    cS
    clmhm
    co
    #
    crab
    #
    wcel
    #
    w3a
    @0
    @1
    wa
    #
    @6
    wa
    #
    cF
    @4
    wcel
    #
    cB
    cC
    cF
    wf1o
    #
    wa
    #
    clmod
    clmod
    va
    cv
    #
    cbs
    cfv
    #
    vb
    cv
    #
    cbs
    cfv
    #
    @2
    wf1o
    #
    vc
    @12
    @14
    clmhm
    co
    #
    crab
    clmim
    @5
    cF
    cR
    cS
    va
    vb
    vb
    vc
    va
    df-lmim
    @16
    vc
    @17
    @12
    @14
    clmhm
    ovex
    rabex
    @12
    cR
    wceq
    #
    @14
    cS
    wceq
    #
    wa
    @16
    @3
    vc
    @17
    @4
    @12
    cR
    @14
    cS
    clmhm
    oveq12
    @18
    @13
    cB
    wceq
    @15
    cC
    wceq
    @16
    @3
    wb
    @19
    @18
    @13
    cR
    cbs
    cfv
    cB
    @12
    cR
    cbs
    fveq2
    islmim.b
    syl6eqr
    @19
    @15
    cS
    cbs
    cfv
    cC
    @14
    cS
    cbs
    fveq2
    islmim.c
    syl6eqr
    @13
    cB
    @15
    cC
    @2
    f1oeq23
    syl2an
    rabeqbidv
    elovmpt2
    @0
    @1
    @6
    df-3an
    @8
    @7
    @11
    wa
    @11
    @6
    @11
    @7
    @3
    @10
    vc
    cF
    @4
    cB
    cC
    @2
    cF
    f1oeq1
    elrab
    anbi2i
    @11
    @7
    @9
    @7
    @10
    @9
    @0
    @1
    cR
    cS
    cF
    lmhmlmod1
    cR
    cS
    cF
    lmhmlmod2
    jca
    adantr
    pm4.71ri
    bitr4i
    3bitri
end
