include "crrx.mm"
include "cfv.mm"
include "ctopn.mm"
include "cbs.mm"
include "crefld.mm"
include "cv.mm"
include "cmin.mm"
include "co.mm"
include "c2.mm"
include "cexp.mm"
include "cmpt.mm"
include "cgsu.mm"
include "csqrt.mm"
include "cmpt2.mm"
include "cmopn.mm"
include "cr.mm"
include "cmap.mm"
include "csu.mm"
include "cfn.mm"
include "rrxtopn.mm"
include "eqid.mm"
include "rrxbasefi.mm"
include "wceq.mm"
include "wcel.mm"
include "adantr.mm"
include "wa.mm"
include "simpl.mm"
include "simprl.mm"
include "simpr.mm"
include "eleqtrd.mm"
include "syldan.mm"
include "simprr.mm"
include "w3a.mm"
include "cc0.mm"
include "csupp.mm"
include "wf.mm"
include "cfsupp.mm"
include "wbr.mm"
include "elmapi.mm"
include "ffvelrnda.mm"
include "adantl.mm"
include "resubcld.mm"
include "resqcld.mm"
include "fmptd.mm"
include "3adant1.mm"
include "3ad2ant1.mm"
include "0red.mm"
include "fidmfisupp.mm"
include "regsumsupp.mm"
include "syl3anc.mm"
include "cc.mm"
include "wss.mm"
include "ax-resscn.mm"
include "a1i.mm"
include "fssd.mm"
include "3ad2ant2.mm"
include "3ad2ant3.mm"
include "subcld.mm"
include "sqcld.mm"
include "fsumsupp0.mm"
include "cvv.mm"
include "eqidd.mm"
include "fveq2.mm"
include "oveq12d.mm"
include "oveq1d.mm"
include "ovexd.mm"
include "fvmptd.mm"
include "sumeq2dv.mm"
include "3eqtrd.mm"
include "fveq2d.mm"
include "mpt2eq123dva.mm"
include "eqtrd.mm"

theorem rrxtopnfi
  let wph: wff ph
  let vf: setvar f
  let vg: setvar g
  let vk: setvar k
  let cI: class I
  let vx: setvar x
  assume rrxtopnfi.1: |- ( ph -> I e. Fin )

  disjoint I f
  disjoint I g
  disjoint I k
  disjoint f g
  disjoint f k
  disjoint g k
  disjoint f ph
  disjoint g ph
  disjoint k ph
  disjoint I x
  disjoint f x
  disjoint g x
  disjoint k x
  disjoint ph x
  disjoint k x
  assert |- ( ph -> ( TopOpen ` ( RR^ ` I ) ) = ( MetOpen ` ( f e. ( RR ^m I ) , g e. ( RR ^m I ) |-> ( sqrt ` sum_ k e. I ( ( ( f ` k ) - ( g ` k ) ) ^ 2 ) ) ) ) )

  proof
    wph
    cI
    crrx
    cfv
    #
    ctopn
    cfv
    vf
    vg
    @0
    cbs
    cfv
    #
    @1
    crefld
    vx
    cI
    vx
    cv
    #
    vf
    cv
    #
    cfv
    #
    @2
    vg
    cv
    #
    cfv
    #
    cmin
    co
    #
    c2
    cexp
    co
    #
    cmpt
    #
    cgsu
    co
    #
    csqrt
    cfv
    #
    cmpt2
    #
    cmopn
    cfv
    vf
    vg
    cr
    cI
    cmap
    co
    #
    @13
    cI
    vk
    cv
    #
    @3
    cfv
    #
    @14
    @5
    cfv
    #
    cmin
    co
    #
    c2
    cexp
    co
    #
    vk
    csu
    #
    csqrt
    cfv
    #
    cmpt2
    #
    cmopn
    cfv
    wph
    vx
    vf
    vg
    cI
    cfn
    rrxtopnfi.1
    rrxtopn
    wph
    @12
    @21
    cmopn
    wph
    vf
    vg
    @1
    @1
    @11
    @13
    @13
    @20
    wph
    @1
    @0
    cI
    rrxtopnfi.1
    @0
    eqid
    @1
    eqid
    rrxbasefi
    #
    wph
    @1
    @13
    wceq
    #
    @3
    @1
    wcel
    #
    @22
    adantr
    #
    wph
    @24
    @5
    @1
    wcel
    #
    wa
    #
    wa
    wph
    @3
    @13
    wcel
    #
    @5
    @13
    wcel
    #
    @11
    @20
    wceq
    wph
    @27
    simpl
    wph
    @27
    @24
    @28
    wph
    @24
    @26
    simprl
    wph
    @24
    wa
    @3
    @1
    @13
    wph
    @24
    simpr
    @25
    eleqtrd
    syldan
    wph
    @27
    @26
    @29
    wph
    @24
    @26
    simprr
    wph
    @26
    wa
    @5
    @1
    @13
    wph
    @26
    simpr
    wph
    @23
    @26
    @22
    adantr
    eleqtrd
    syldan
    wph
    @28
    @29
    w3a
    #
    @10
    @19
    csqrt
    @30
    @10
    @9
    cc0
    csupp
    co
    @14
    @9
    cfv
    #
    vk
    csu
    #
    cI
    @31
    vk
    csu
    @19
    @30
    cI
    cr
    @9
    wf
    #
    @9
    cc0
    cfsupp
    wbr
    cI
    cfn
    wcel
    #
    @10
    @32
    wceq
    @28
    @29
    @33
    wph
    @28
    @29
    wa
    #
    vx
    cI
    @8
    cr
    @9
    @35
    @2
    cI
    wcel
    #
    wa
    #
    @7
    @37
    @4
    @6
    @35
    cI
    cr
    @2
    @3
    @28
    cI
    cr
    @3
    wf
    @29
    @3
    cr
    cI
    elmapi
    #
    adantr
    ffvelrnda
    @35
    cI
    cr
    @2
    @5
    @29
    cI
    cr
    @5
    wf
    @28
    @5
    cr
    cI
    elmapi
    #
    adantl
    ffvelrnda
    resubcld
    resqcld
    @9
    eqid
    #
    fmptd
    3adant1
    #
    @30
    cI
    cr
    @9
    cr
    cc0
    @41
    wph
    @28
    @34
    @29
    rrxtopnfi.1
    3ad2ant1
    #
    @30
    0red
    fidmfisupp
    @42
    vk
    @9
    cI
    cfn
    regsumsupp
    syl3anc
    @30
    cI
    vk
    @9
    @42
    @30
    vx
    cI
    @8
    cc
    @9
    @30
    @36
    wa
    #
    @7
    @43
    @4
    @6
    @30
    cI
    cc
    @2
    @3
    @28
    wph
    cI
    cc
    @3
    wf
    @29
    @28
    cI
    cr
    cc
    @3
    @38
    cr
    cc
    wss
    #
    @28
    ax-resscn
    a1i
    fssd
    3ad2ant2
    ffvelrnda
    @30
    cI
    cc
    @2
    @5
    @29
    wph
    cI
    cc
    @5
    wf
    @28
    @29
    cI
    cr
    cc
    @5
    @39
    @44
    @29
    ax-resscn
    a1i
    fssd
    3ad2ant3
    ffvelrnda
    subcld
    sqcld
    @40
    fmptd
    fsumsupp0
    @30
    cI
    @31
    @18
    vk
    @30
    @14
    cI
    wcel
    #
    wa
    #
    vx
    @14
    @8
    @18
    cI
    @9
    cvv
    @46
    @9
    eqidd
    @2
    @14
    wceq
    #
    @8
    @18
    wceq
    @46
    @47
    @7
    @17
    c2
    cexp
    @47
    @4
    @15
    @6
    @16
    cmin
    @2
    @14
    @3
    fveq2
    @2
    @14
    @5
    fveq2
    oveq12d
    oveq1d
    adantl
    @30
    @45
    simpr
    @46
    @17
    c2
    cexp
    ovexd
    fvmptd
    sumeq2dv
    3eqtrd
    fveq2d
    syl3anc
    mpt2eq123dva
    fveq2d
    eqtrd
end
