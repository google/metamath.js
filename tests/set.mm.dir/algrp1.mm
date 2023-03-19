include "wcel.mm"
include "wa.mm"
include "c1.mm"
include "caddc.mm"
include "co.mm"
include "c1st.mm"
include "ccom.mm"
include "csn.mm"
include "cxp.mm"
include "cseq.mm"
include "cfv.mm"
include "cuz.mm"
include "wceq.mm"
include "simpr.mm"
include "syl6eleq.mm"
include "seqp1.mm"
include "syl.mm"
include "fveq1i.mm"
include "fveq2i.mm"
include "fvex.mm"
include "algrflem.mm"
include "eqtr4i.mm"
include "3eqtr4g.mm"

theorem algrp1
  let wph: wff ph
  let cA: class A
  let cR: class R
  let cS: class S
  let cF: class F
  let cK: class K
  let cM: class M
  let cZ: class Z
  let vx: setvar x
  let vy: setvar y
  let cV: class V
  assume algrf.1: |- Z = ( ZZ>= ` M )
  assume algrf.2: |- R = seq M ( ( F o. 1st ) , ( Z X. { A } ) )
  assume algrf.3: |- ( ph -> M e. ZZ )
  assume algrf.4: |- ( ph -> A e. S )
  assume algrf.5: |- ( ph -> F : S --> S )


  assert |- ( ( ph /\ K e. Z ) -> ( R ` ( K + 1 ) ) = ( F ` ( R ` K ) ) )

  proof
    wph
    cK
    cZ
    wcel
    #
    wa
    #
    cK
    c1
    caddc
    co
    #
    cF
    c1st
    ccom
    #
    cZ
    cA
    csn
    cxp
    #
    cM
    cseq
    #
    cfv
    #
    cK
    @5
    cfv
    #
    @2
    @4
    cfv
    #
    @3
    co
    #
    @2
    cR
    cfv
    cK
    cR
    cfv
    #
    cF
    cfv
    #
    @1
    cK
    cM
    cuz
    cfv
    #
    wcel
    @6
    @9
    wceq
    @1
    cK
    cZ
    @12
    wph
    @0
    simpr
    algrf.1
    syl6eleq
    @3
    @4
    cM
    cK
    seqp1
    syl
    @2
    cR
    @5
    algrf.2
    fveq1i
    @11
    @7
    cF
    cfv
    @9
    @10
    @7
    cF
    cK
    cR
    @5
    algrf.2
    fveq1i
    fveq2i
    @7
    @8
    cF
    cK
    @5
    fvex
    @2
    @4
    fvex
    algrflem
    eqtr4i
    3eqtr4g
end
