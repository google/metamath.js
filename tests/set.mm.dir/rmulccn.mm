include "cc.mm"
include "cv.mm"
include "cmul.mm"
include "co.mm"
include "cmpt.mm"
include "cr.mm"
include "cres.mm"
include "ccnfld.mm"
include "ctopn.mm"
include "cfv.mm"
include "crest.mm"
include "ccn.mm"
include "wcel.mm"
include "wss.mm"
include "ctopon.mm"
include "eqid.mm"
include "cnfldtopon.mm"
include "a1i.mm"
include "cnmptid.mm"
include "recnd.mm"
include "cnmptc.mm"
include "cmpt2.mm"
include "ctx.mm"
include "cxp.mm"
include "wfn.mm"
include "wceq.mm"
include "wf.mm"
include "ax-mulf.mm"
include "ffn.mm"
include "ax-mp.mm"
include "fnov.mm"
include "mpbi.mm"
include "mulcn.mm"
include "eqeltrri.mm"
include "oveq12.mm"
include "cnmpt12.mm"
include "ax-resscn.mm"
include "toponunii.mm"
include "cnrest.mm"
include "sylancl.mm"
include "crn.mm"
include "wb.mm"
include "wral.mm"
include "wa.mm"
include "simpr.mm"
include "adantr.mm"
include "mulcld.mm"
include "ralrimiva.mm"
include "fnmpt.mm"
include "syl.mm"
include "fnssres.mm"
include "fvres.mm"
include "recn.mm"
include "oveq1.mm"
include "ovex.mm"
include "fvmpt.mm"
include "eqtrd.mm"
include "remulcld.mm"
include "eqeltrd.mm"
include "fnfvrnss.mm"
include "syl2anc.mm"
include "cnrest2.mm"
include "syl3anc.mm"
include "mpbid.mm"
include "resmpt.mm"
include "cioo.mm"
include "ctg.mm"
include "tgioo2.mm"
include "eqtri.mm"
include "oveq12i.mm"
include "eqcomi.mm"
include "3eltr3g.mm"

theorem rmulccn
  let wph: wff ph
  let vx: setvar x
  let cC: class C
  let cJ: class J
  let vw: setvar w
  let vy: setvar y
  let vz: setvar z
  assume rmulccn.1: |- J = ( topGen ` ran (,) )
  assume rmulccn.2: |- ( ph -> C e. RR )

  disjoint C x
  disjoint ph x
  disjoint w x
  disjoint C w
  disjoint ph w
  disjoint x y
  disjoint x z
  disjoint y z
  disjoint C y
  disjoint C z
  assert |- ( ph -> ( x e. RR |-> ( x x. C ) ) e. ( J Cn J ) )

  proof
    wph
    vx
    cc
    vx
    cv
    #
    cC
    cmul
    co
    #
    cmpt
    #
    cr
    cres
    #
    ccnfld
    ctopn
    cfv
    #
    cr
    crest
    co
    #
    @5
    ccn
    co
    #
    vx
    cr
    @1
    cmpt
    #
    cJ
    cJ
    ccn
    co
    #
    wph
    @3
    @5
    @4
    ccn
    co
    wcel
    #
    @3
    @6
    wcel
    #
    wph
    @2
    @4
    @4
    ccn
    co
    wcel
    cr
    cc
    wss
    #
    @9
    wph
    vx
    vy
    vz
    @0
    cC
    vy
    cv
    #
    vz
    cv
    #
    cmul
    co
    #
    @1
    @4
    @4
    @4
    @4
    cc
    cc
    cc
    @4
    cc
    ctopon
    cfv
    wcel
    #
    wph
    @4
    @4
    eqid
    #
    cnfldtopon
    #
    a1i
    #
    wph
    vx
    @4
    cc
    @18
    cnmptid
    wph
    vx
    cC
    @4
    @4
    cc
    cc
    @18
    @18
    wph
    cC
    rmulccn.2
    recnd
    #
    cnmptc
    @18
    @18
    vy
    vz
    cc
    cc
    @14
    cmpt2
    #
    @4
    @4
    ctx
    co
    @4
    ccn
    co
    #
    wcel
    wph
    cmul
    @20
    @21
    cmul
    cc
    cc
    cxp
    #
    wfn
    #
    cmul
    @20
    wceq
    @22
    cc
    cmul
    wf
    @23
    ax-mulf
    @22
    cc
    cmul
    ffn
    ax-mp
    vy
    vz
    cc
    cc
    cmul
    fnov
    mpbi
    @4
    @16
    mulcn
    eqeltrri
    a1i
    @12
    @0
    @13
    cC
    cmul
    oveq12
    cnmpt12
    ax-resscn
    cr
    @2
    @4
    @4
    cc
    cc
    @4
    @17
    toponunii
    cnrest
    sylancl
    wph
    @15
    @3
    crn
    cr
    wss
    #
    @11
    @9
    @10
    wb
    @18
    wph
    @3
    cr
    wfn
    #
    vw
    cv
    #
    @3
    cfv
    #
    cr
    wcel
    #
    vw
    cr
    wral
    @24
    wph
    @2
    cc
    wfn
    #
    @11
    @25
    wph
    @1
    cc
    wcel
    #
    vx
    cc
    wral
    @29
    wph
    @30
    vx
    cc
    wph
    @0
    cc
    wcel
    #
    wa
    @0
    cC
    wph
    @31
    simpr
    wph
    cC
    cc
    wcel
    @31
    @19
    adantr
    mulcld
    ralrimiva
    vx
    cc
    @1
    @2
    cc
    @2
    eqid
    #
    fnmpt
    syl
    ax-resscn
    cc
    cr
    @2
    fnssres
    sylancl
    wph
    @28
    vw
    cr
    wph
    @26
    cr
    wcel
    #
    wa
    #
    @27
    @26
    cC
    cmul
    co
    #
    cr
    @34
    @33
    @27
    @35
    wceq
    wph
    @33
    simpr
    #
    @33
    @27
    @26
    @2
    cfv
    #
    @35
    @26
    cr
    @2
    fvres
    @33
    @26
    cc
    wcel
    @37
    @35
    wceq
    @26
    recn
    vx
    @26
    @1
    @35
    cc
    @2
    @0
    @26
    cC
    cmul
    oveq1
    @32
    @26
    cC
    cmul
    ovex
    fvmpt
    syl
    eqtrd
    syl
    @34
    @26
    cC
    @36
    wph
    cC
    cr
    wcel
    @33
    rmulccn.2
    adantr
    remulcld
    eqeltrd
    ralrimiva
    vw
    cr
    cr
    @3
    fnfvrnss
    syl2anc
    @11
    wph
    ax-resscn
    a1i
    cr
    @3
    @5
    @4
    cc
    cnrest2
    syl3anc
    mpbid
    @11
    @3
    @7
    wceq
    ax-resscn
    vx
    cc
    cr
    @1
    resmpt
    ax-mp
    @8
    @6
    cJ
    @5
    cJ
    @5
    ccn
    cJ
    cioo
    crn
    ctg
    cfv
    @5
    rmulccn.1
    @4
    @16
    tgioo2
    eqtri
    #
    @38
    oveq12i
    eqcomi
    3eltr3g
end
