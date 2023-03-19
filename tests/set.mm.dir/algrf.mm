include "c1st.mm"
include "ccom.mm"
include "csn.mm"
include "cxp.mm"
include "cseq.mm"
include "wf.mm"
include "cv.mm"
include "wcel.mm"
include "wa.mm"
include "cfv.mm"
include "wceq.mm"
include "fvconst2g.mm"
include "sylan.mm"
include "adantr.mm"
include "eqeltrd.mm"
include "co.mm"
include "vex.mm"
include "algrflem.mm"
include "simpl.mm"
include "ffvelrn.mm"
include "syl2an.mm"
include "syl5eqel.mm"
include "seqf.mm"
include "feq1i.mm"
include "sylibr.mm"

theorem algrf
  let wph: wff ph
  let cA: class A
  let cR: class R
  let cS: class S
  let cF: class F
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


  assert |- ( ph -> R : Z --> S )

  proof
    wph
    cZ
    cS
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
    wf
    cZ
    cS
    cR
    wf
    wph
    vx
    vy
    @0
    cS
    @1
    cM
    cZ
    algrf.1
    algrf.3
    wph
    vx
    cv
    #
    cZ
    wcel
    #
    wa
    @3
    @1
    cfv
    #
    cA
    cS
    wph
    cA
    cS
    wcel
    #
    @4
    @5
    cA
    wceq
    algrf.4
    cZ
    cA
    @3
    cS
    fvconst2g
    sylan
    wph
    @6
    @4
    algrf.4
    adantr
    eqeltrd
    wph
    @3
    cS
    wcel
    #
    vy
    cv
    #
    cS
    wcel
    #
    wa
    #
    wa
    @3
    @8
    @0
    co
    @3
    cF
    cfv
    #
    cS
    @3
    @8
    cF
    vx
    vex
    vy
    vex
    algrflem
    wph
    cS
    cS
    cF
    wf
    @7
    @11
    cS
    wcel
    @10
    algrf.5
    @7
    @9
    simpl
    cS
    cS
    @3
    cF
    ffvelrn
    syl2an
    syl5eqel
    seqf
    cZ
    cS
    cR
    @2
    algrf.2
    feq1i
    sylibr
end
