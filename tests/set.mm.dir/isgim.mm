include "cgrp.mm"
include "wcel.mm"
include "cv.mm"
include "wf1o.mm"
include "cghm.mm"
include "co.mm"
include "crab.mm"
include "w3a.mm"
include "wa.mm"
include "cgim.mm"
include "df-3an.mm"
include "cbs.mm"
include "cfv.mm"
include "df-gim.mm"
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
include "ghmgrp1.mm"
include "ghmgrp2.mm"
include "jca.mm"
include "adantr.mm"
include "pm4.71ri.mm"
include "f1oeq1.mm"
include "elrab.mm"
include "anbi2i.mm"
include "bitr4i.mm"
include "3bitr4i.mm"

theorem isgim
  let cB: class B
  let cC: class C
  let cR: class R
  let cS: class S
  let cF: class F
  let va: setvar a
  let vb: setvar b
  let vc: setvar c
  assume isgim.b: |- B = ( Base ` R )
  assume isgim.c: |- C = ( Base ` S )


  assert |- ( F e. ( R GrpIso S ) <-> ( F e. ( R GrpHom S ) /\ F : B -1-1-onto-> C ) )

  proof
    cR
    cgrp
    wcel
    #
    cS
    cgrp
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
    cghm
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
    cR
    cS
    cgim
    co
    wcel
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
    @0
    @1
    @6
    df-3an
    cgrp
    cgrp
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
    cghm
    co
    #
    crab
    cgim
    @5
    cF
    cR
    cS
    va
    vb
    vb
    vc
    va
    df-gim
    @16
    vc
    @17
    @12
    @14
    cghm
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
    cghm
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
    isgim.b
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
    isgim.c
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
    @11
    @7
    @11
    wa
    @8
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
    ghmgrp1
    cR
    cS
    cF
    ghmgrp2
    jca
    adantr
    pm4.71ri
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
    bitr4i
    3bitr4i
end
