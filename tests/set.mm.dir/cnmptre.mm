include "cmpt.mm"
include "crest.mm"
include "co.mm"
include "ccn.mm"
include "wcel.mm"
include "cc.mm"
include "eqid.mm"
include "ctopon.mm"
include "cfv.mm"
include "cnfldtopon.mm"
include "a1i.mm"
include "cr.mm"
include "ax-resscn.mm"
include "syl6ss.mm"
include "cnmpt1res.mm"
include "cioo.mm"
include "crn.mm"
include "ctg.mm"
include "wss.mm"
include "wceq.mm"
include "rerest.mm"
include "syl.mm"
include "syl6eqr.mm"
include "oveq1d.mm"
include "eleqtrd.mm"
include "wb.mm"
include "wf.mm"
include "fmptd.mm"
include "frn.mm"
include "cnrest2.mm"
include "syl3anc.mm"
include "mpbid.mm"
include "oveq2d.mm"

theorem cnmptre
  let wph: wff ph
  let vx: setvar x
  let cA: class A
  let cB: class B
  let cR: class R
  let cF: class F
  let cJ: class J
  let cK: class K
  assume cnmptre.1: |- R = ( TopOpen ` CCfld )
  assume cnmptre.2: |- J = ( ( topGen ` ran (,) ) |`t A )
  assume cnmptre.3: |- K = ( ( topGen ` ran (,) ) |`t B )
  assume cnmptre.4: |- ( ph -> A C_ RR )
  assume cnmptre.5: |- ( ph -> B C_ RR )
  assume cnmptre.6: |- ( ( ph /\ x e. A ) -> F e. B )
  assume cnmptre.7: |- ( ph -> ( x e. CC |-> F ) e. ( R Cn R ) )

  disjoint A x
  disjoint B x
  disjoint ph x
  assert |- ( ph -> ( x e. A |-> F ) e. ( J Cn K ) )

  proof
    wph
    vx
    cA
    cF
    cmpt
    #
    cJ
    cR
    cB
    crest
    co
    #
    ccn
    co
    #
    cJ
    cK
    ccn
    co
    wph
    @0
    cJ
    cR
    ccn
    co
    #
    wcel
    #
    @0
    @2
    wcel
    #
    wph
    @0
    cR
    cA
    crest
    co
    #
    cR
    ccn
    co
    @3
    wph
    vx
    cF
    cR
    @6
    cR
    cc
    cA
    @6
    eqid
    cR
    cc
    ctopon
    cfv
    wcel
    #
    wph
    cR
    cnmptre.1
    cnfldtopon
    a1i
    #
    wph
    cA
    cr
    cc
    cnmptre.4
    ax-resscn
    syl6ss
    cnmptre.7
    cnmpt1res
    wph
    @6
    cJ
    cR
    ccn
    wph
    @6
    cioo
    crn
    ctg
    cfv
    #
    cA
    crest
    co
    #
    cJ
    wph
    cA
    cr
    wss
    @6
    @10
    wceq
    cnmptre.4
    cA
    @9
    cR
    cnmptre.1
    @9
    eqid
    #
    rerest
    syl
    cnmptre.2
    syl6eqr
    oveq1d
    eleqtrd
    wph
    @7
    @0
    crn
    cB
    wss
    #
    cB
    cc
    wss
    @4
    @5
    wb
    @8
    wph
    cA
    cB
    @0
    wf
    @12
    wph
    vx
    cA
    cF
    cB
    @0
    cnmptre.6
    @0
    eqid
    fmptd
    cA
    cB
    @0
    frn
    syl
    wph
    cB
    cr
    cc
    cnmptre.5
    ax-resscn
    syl6ss
    cB
    @0
    cJ
    cR
    cc
    cnrest2
    syl3anc
    mpbid
    wph
    @1
    cK
    cJ
    ccn
    wph
    @1
    @9
    cB
    crest
    co
    #
    cK
    wph
    cB
    cr
    wss
    @1
    @13
    wceq
    cnmptre.5
    cB
    @9
    cR
    cnmptre.1
    @11
    rerest
    syl
    cnmptre.3
    syl6eqr
    oveq2d
    eleqtrd
end
