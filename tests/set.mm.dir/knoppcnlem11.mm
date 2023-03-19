include "cn0.mm"
include "cr.mm"
include "cc.mm"
include "ccncf.mm"
include "co.mm"
include "cv.mm"
include "caddc.mm"
include "cof.mm"
include "cfv.mm"
include "cmpt.mm"
include "cc0.mm"
include "cseq.mm"
include "wf.mm"
include "wcel.mm"
include "wa.mm"
include "cfz.mm"
include "csu.mm"
include "cn.mm"
include "adantr.mm"
include "simpr.mm"
include "knoppcnlem7.mm"
include "eqidd.mm"
include "cuz.mm"
include "simplr.mm"
include "elnn0uz.mm"
include "sylib.mm"
include "ad2antrr.mm"
include "elfzuz.mm"
include "nn0uz.mm"
include "syl6eleqr.mm"
include "adantl.mm"
include "knoppcnlem3.mm"
include "recnd.mm"
include "fsumser.mm"
include "eqcomd.mm"
include "mpteq2dva.mm"
include "eqtrd.mm"
include "cioo.mm"
include "crn.mm"
include "ctg.mm"
include "ccnfld.mm"
include "ctopn.mm"
include "ccn.mm"
include "eqid.mm"
include "ctopon.mm"
include "retopon.mm"
include "a1i.mm"
include "fzfid.mm"
include "knoppcnlem10.mm"
include "fsumcn.mm"
include "wss.mm"
include "wceq.mm"
include "ax-resscn.mm"
include "ssid.mm"
include "pm3.2i.mm"
include "tgioo2.mm"
include "crest.mm"
include "cvv.mm"
include "fvex.mm"
include "cnfldtopon.mm"
include "toponunii.mm"
include "restid.mm"
include "ax-mp.mm"
include "eqcomi.mm"
include "cncfcn.mm"
include "eqeltrd.mm"
include "fmptd.mm"
include "wfn.mm"
include "cz.mm"
include "0z.mm"
include "seqfn.mm"
include "fneq2i.mm"
include "mpbir.mm"
include "dffn5.mm"
include "mpbi.mm"
include "feq1i.mm"
include "sylibr.mm"

theorem knoppcnlem11
  let wph: wff ph
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let cC: class C
  let cT: class T
  let vm: setvar m
  let vn: setvar n
  let cF: class F
  let cN: class N
  let vw: setvar w
  let vk: setvar k
  let vl: setvar l
  assume knoppcnlem11.t: |- T = ( x e. RR |-> ( abs ` ( ( |_ ` ( x + ( 1 / 2 ) ) ) - x ) ) )
  assume knoppcnlem11.f: |- F = ( y e. RR |-> ( n e. NN0 |-> ( ( C ^ n ) x. ( T ` ( ( ( 2 x. N ) ^ n ) x. y ) ) ) ) )
  assume knoppcnlem11.n: |- ( ph -> N e. NN )
  assume knoppcnlem11.1: |- ( ph -> C e. RR )

  disjoint C n
  disjoint C y
  disjoint n y
  disjoint F m
  disjoint F z
  disjoint m z
  disjoint N n
  disjoint N y
  disjoint N x
  disjoint T n
  disjoint T y
  disjoint n ph
  disjoint ph y
  disjoint m ph
  disjoint C w
  disjoint n w
  disjoint w y
  disjoint F k
  disjoint F l
  disjoint F w
  disjoint k l
  disjoint k w
  disjoint l w
  disjoint k m
  disjoint k z
  disjoint m w
  disjoint w z
  disjoint N w
  disjoint w x
  disjoint T w
  disjoint k ph
  disjoint l ph
  disjoint ph w
  disjoint k n
  disjoint k y
  disjoint l n
  disjoint l y
  disjoint l x
  assert |- ( ph -> seq 0 ( oF + , ( m e. NN0 |-> ( z e. RR |-> ( ( F ` z ) ` m ) ) ) ) : NN0 --> ( RR -cn-> CC ) )

  proof
    wph
    cn0
    cr
    cc
    ccncf
    co
    #
    vk
    cn0
    vk
    cv
    #
    caddc
    cof
    #
    vm
    cn0
    vz
    cr
    vm
    cv
    vz
    cv
    cF
    cfv
    cfv
    cmpt
    cmpt
    #
    cc0
    cseq
    #
    cfv
    #
    cmpt
    #
    wf
    cn0
    @0
    @4
    wf
    wph
    vk
    cn0
    @5
    @0
    @6
    wph
    @1
    cn0
    wcel
    #
    wa
    #
    @5
    vw
    cr
    cc0
    @1
    cfz
    co
    #
    vl
    cv
    #
    vw
    cv
    #
    cF
    cfv
    #
    cfv
    #
    vl
    csu
    #
    cmpt
    #
    @0
    @8
    @5
    vw
    cr
    @1
    caddc
    @12
    cc0
    cseq
    cfv
    #
    cmpt
    @15
    @8
    vx
    vy
    vz
    vw
    cC
    cT
    vm
    vn
    cF
    @1
    cN
    knoppcnlem11.t
    knoppcnlem11.f
    wph
    cN
    cn
    wcel
    #
    @7
    knoppcnlem11.n
    adantr
    #
    wph
    cC
    cr
    wcel
    #
    @7
    knoppcnlem11.1
    adantr
    #
    wph
    @7
    simpr
    knoppcnlem7
    @8
    vw
    cr
    @16
    @14
    @8
    @11
    cr
    wcel
    #
    wa
    #
    @14
    @16
    @22
    @13
    vl
    @12
    cc0
    @1
    @22
    @10
    @9
    wcel
    #
    wa
    #
    @13
    eqidd
    @22
    @7
    @1
    cc0
    cuz
    cfv
    #
    wcel
    wph
    @7
    @21
    simplr
    @1
    elnn0uz
    sylib
    @24
    @13
    @24
    vx
    vy
    @11
    cC
    cT
    vn
    cF
    @10
    cN
    knoppcnlem11.t
    knoppcnlem11.f
    @8
    @17
    @21
    @23
    @18
    ad2antrr
    @8
    @19
    @21
    @23
    @20
    ad2antrr
    @8
    @21
    @23
    simplr
    @23
    @10
    cn0
    wcel
    #
    @22
    @23
    @10
    @25
    cn0
    @10
    cc0
    @1
    elfzuz
    nn0uz
    syl6eleqr
    #
    adantl
    knoppcnlem3
    recnd
    fsumser
    eqcomd
    mpteq2dva
    eqtrd
    @8
    @15
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
    @0
    @8
    vw
    @9
    @13
    vl
    @28
    @29
    cr
    @29
    eqid
    #
    @28
    cr
    ctopon
    cfv
    wcel
    @8
    retopon
    a1i
    @8
    cc0
    @1
    fzfid
    @8
    @23
    wa
    vx
    vy
    vw
    cC
    cT
    vn
    cF
    @10
    cN
    knoppcnlem11.t
    knoppcnlem11.f
    @8
    @17
    @23
    @18
    adantr
    @8
    @19
    @23
    @20
    adantr
    @23
    @26
    @8
    @27
    adantl
    knoppcnlem10
    fsumcn
    cr
    cc
    wss
    #
    cc
    cc
    wss
    #
    wa
    @0
    @30
    wceq
    @32
    @33
    ax-resscn
    cc
    ssid
    pm3.2i
    cr
    cc
    @29
    @28
    @29
    @31
    @29
    @31
    tgioo2
    @29
    cc
    crest
    co
    #
    @29
    @29
    cvv
    wcel
    @34
    @29
    wceq
    ccnfld
    ctopn
    fvex
    @29
    cvv
    cc
    cc
    @29
    @29
    @31
    cnfldtopon
    toponunii
    restid
    ax-mp
    eqcomi
    cncfcn
    ax-mp
    syl6eleqr
    eqeltrd
    @6
    eqid
    fmptd
    cn0
    @0
    @4
    @6
    @4
    cn0
    wfn
    #
    @4
    @6
    wceq
    @35
    @4
    @25
    wfn
    #
    cc0
    cz
    wcel
    @36
    0z
    @2
    @3
    cc0
    seqfn
    ax-mp
    cn0
    @25
    @4
    nn0uz
    fneq2i
    mpbir
    vk
    cn0
    @4
    dffn5
    mpbi
    feq1i
    sylibr
end
