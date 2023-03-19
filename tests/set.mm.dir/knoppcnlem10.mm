include "cr.mm"
include "cv.mm"
include "cfv.mm"
include "cmpt.mm"
include "cexp.mm"
include "co.mm"
include "c2.mm"
include "cmul.mm"
include "cioo.mm"
include "crn.mm"
include "ctg.mm"
include "ccnfld.mm"
include "ctopn.mm"
include "ccn.mm"
include "wcel.mm"
include "wa.mm"
include "simpr.mm"
include "cn0.mm"
include "adantr.mm"
include "knoppcnlem1.mm"
include "mpteq2dva.mm"
include "ctopon.mm"
include "retopon.mm"
include "a1i.mm"
include "cc.mm"
include "eqid.mm"
include "cnfldtopon.mm"
include "recnd.mm"
include "expcld.mm"
include "cnmptc.mm"
include "crest.mm"
include "2re.mm"
include "cn.mm"
include "nnre.mm"
include "syl.mm"
include "remulcld.mm"
include "reexpcld.mm"
include "tgioo2.mm"
include "oveq2i.mm"
include "ctop.mm"
include "wss.mm"
include "topontopi.mm"
include "cnrest2r.mm"
include "ax-mp.mm"
include "eqsstri.mm"
include "cnmptid.mm"
include "sseldi.mm"
include "ctx.mm"
include "mulcn.mm"
include "cnmpt12f.mm"
include "w3a.mm"
include "wb.mm"
include "wf.mm"
include "fmptd.mm"
include "frn.mm"
include "ax-resscn.mm"
include "3jca.mm"
include "cnrest2.mm"
include "mpbid.mm"
include "syl6eleqr.mm"
include "ccncf.mm"
include "ssid.mm"
include "pm3.2i.mm"
include "cncfss.mm"
include "dnicn.mm"
include "wceq.mm"
include "cvv.mm"
include "fvex.mm"
include "toponunii.mm"
include "restid.mm"
include "eqcomi.mm"
include "cncfcn.mm"
include "syl6eleq.mm"
include "cnmpt11f.mm"
include "eqeltrd.mm"

theorem knoppcnlem10
  let wph: wff ph
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let cC: class C
  let cT: class T
  let vn: setvar n
  let cF: class F
  let cM: class M
  let cN: class N
  assume knoppcnlem10.t: |- T = ( x e. RR |-> ( abs ` ( ( |_ ` ( x + ( 1 / 2 ) ) ) - x ) ) )
  assume knoppcnlem10.f: |- F = ( y e. RR |-> ( n e. NN0 |-> ( ( C ^ n ) x. ( T ` ( ( ( 2 x. N ) ^ n ) x. y ) ) ) ) )
  assume knoppcnlem10.n: |- ( ph -> N e. NN )
  assume knoppcnlem10.1: |- ( ph -> C e. RR )
  assume knoppcnlem10.2: |- ( ph -> M e. NN0 )

  disjoint C n
  disjoint C y
  disjoint C z
  disjoint n y
  disjoint n z
  disjoint y z
  disjoint M n
  disjoint M z
  disjoint N n
  disjoint N y
  disjoint N z
  disjoint T n
  disjoint T y
  disjoint T z
  disjoint n ph
  disjoint ph y
  disjoint ph z
  assert |- ( ph -> ( z e. RR |-> ( ( F ` z ) ` M ) ) e. ( ( topGen ` ran (,) ) Cn ( TopOpen ` CCfld ) ) )

  proof
    wph
    vz
    cr
    cM
    vz
    cv
    #
    cF
    cfv
    cfv
    #
    cmpt
    vz
    cr
    cC
    cM
    cexp
    co
    #
    c2
    cN
    cmul
    co
    #
    cM
    cexp
    co
    #
    @0
    cmul
    co
    #
    cT
    cfv
    #
    cmul
    co
    #
    cmpt
    cioo
    crn
    ctg
    cfv
    #
    ccnfld
    ctopn
    cfv
    #
    ccn
    co
    #
    wph
    vz
    cr
    @1
    @7
    wph
    @0
    cr
    wcel
    #
    wa
    #
    vy
    @0
    cC
    cT
    vn
    cF
    cM
    cN
    knoppcnlem10.f
    wph
    @11
    simpr
    #
    wph
    cM
    cn0
    wcel
    @11
    knoppcnlem10.2
    adantr
    knoppcnlem1
    mpteq2dva
    wph
    vz
    @2
    @6
    cmul
    @8
    @9
    @9
    @9
    cr
    @8
    cr
    ctopon
    cfv
    wcel
    wph
    retopon
    a1i
    #
    wph
    vz
    @2
    @8
    @9
    cr
    cc
    @14
    @9
    cc
    ctopon
    cfv
    wcel
    #
    wph
    @9
    @9
    eqid
    #
    cnfldtopon
    #
    a1i
    #
    wph
    cC
    cM
    wph
    cC
    knoppcnlem10.1
    recnd
    knoppcnlem10.2
    expcld
    cnmptc
    wph
    vz
    @5
    cT
    @8
    @8
    @9
    cr
    @14
    wph
    vz
    cr
    @5
    cmpt
    #
    @8
    @9
    cr
    crest
    co
    #
    ccn
    co
    #
    @8
    @8
    ccn
    co
    #
    wph
    @19
    @10
    wcel
    #
    @19
    @21
    wcel
    #
    wph
    vz
    @4
    @0
    cmul
    @8
    @9
    @9
    @9
    cr
    @14
    wph
    vz
    @4
    @8
    @9
    cr
    cc
    @14
    @18
    wph
    @4
    wph
    @3
    cM
    wph
    c2
    cN
    c2
    cr
    wcel
    wph
    2re
    a1i
    wph
    cN
    cn
    wcel
    cN
    cr
    wcel
    knoppcnlem10.n
    cN
    nnre
    syl
    remulcld
    knoppcnlem10.2
    reexpcld
    #
    recnd
    cnmptc
    wph
    @22
    @10
    vz
    cr
    @0
    cmpt
    @22
    @21
    @10
    @8
    @20
    @8
    ccn
    @9
    @16
    tgioo2
    #
    oveq2i
    #
    @9
    ctop
    wcel
    @21
    @10
    wss
    cc
    @9
    @17
    topontopi
    cr
    @8
    @9
    cnrest2r
    ax-mp
    eqsstri
    wph
    vz
    @8
    cr
    @14
    cnmptid
    sseldi
    cmul
    @9
    @9
    ctx
    co
    @9
    ccn
    co
    wcel
    wph
    @9
    @16
    mulcn
    a1i
    #
    cnmpt12f
    wph
    @15
    @19
    crn
    cr
    wss
    #
    cr
    cc
    wss
    #
    w3a
    @23
    @24
    wb
    wph
    @15
    @29
    @30
    @18
    wph
    cr
    cr
    @19
    wf
    @29
    wph
    vz
    cr
    @5
    cr
    @19
    @12
    @4
    @0
    wph
    @4
    cr
    wcel
    @11
    @25
    adantr
    @13
    remulcld
    @19
    eqid
    fmptd
    cr
    cr
    @19
    frn
    syl
    @30
    wph
    ax-resscn
    a1i
    3jca
    cr
    @19
    @8
    @9
    cc
    cnrest2
    syl
    mpbid
    @27
    syl6eleqr
    wph
    cT
    cr
    cc
    ccncf
    co
    #
    @10
    wph
    cr
    cr
    ccncf
    co
    #
    @31
    cT
    @30
    cc
    cc
    wss
    #
    wa
    #
    @32
    @31
    wss
    @30
    @33
    ax-resscn
    cc
    ssid
    pm3.2i
    #
    cr
    cr
    cc
    cncfss
    ax-mp
    cT
    @32
    wcel
    wph
    vx
    cT
    knoppcnlem10.t
    dnicn
    a1i
    sseldi
    @34
    @31
    @10
    wceq
    @35
    cr
    cc
    @9
    @8
    @9
    @16
    @26
    @9
    cc
    crest
    co
    #
    @9
    @9
    cvv
    wcel
    @36
    @9
    wceq
    ccnfld
    ctopn
    fvex
    @9
    cvv
    cc
    cc
    @9
    @17
    toponunii
    restid
    ax-mp
    eqcomi
    cncfcn
    ax-mp
    syl6eleq
    cnmpt11f
    @28
    cnmpt12f
    eqeltrd
end
