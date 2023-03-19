include "c2.mm"
include "cuz.mm"
include "cfv.mm"
include "wcel.mm"
include "cn0.mm"
include "cz.mm"
include "cxp.mm"
include "cv.mm"
include "c1st.mm"
include "cexp.mm"
include "co.mm"
include "c1.mm"
include "cmin.mm"
include "csqrt.mm"
include "c2nd.mm"
include "cmul.mm"
include "caddc.mm"
include "cmpt.mm"
include "wfn.mm"
include "crn.mm"
include "wceq.mm"
include "wrex.mm"
include "cab.mm"
include "wi.mm"
include "wral.mm"
include "wf1o.mm"
include "ovex.mm"
include "eqid.mm"
include "fnmpti.mm"
include "a1i.mm"
include "wb.mm"
include "cop.mm"
include "vex.mm"
include "op1std.mm"
include "op2ndd.mm"
include "oveq2d.mm"
include "oveq12d.mm"
include "eqeq2d.mm"
include "rexxp.mm"
include "bicomi.mm"
include "abbidv.mm"
include "rnmpt.mm"
include "syl6reqr.mm"
include "wa.mm"
include "fveq2.mm"
include "fvmpt.mm"
include "ad2antrl.mm"
include "ad2antll.mm"
include "eqeq12d.mm"
include "cc.mm"
include "cq.mm"
include "cdif.mm"
include "rmspecsqrtnq.mm"
include "adantr.mm"
include "nn0ssq.mm"
include "xp1st.mm"
include "sseldi.mm"
include "xp2nd.mm"
include "zq.mm"
include "syl.mm"
include "qirropth.mm"
include "syl122anc.mm"
include "biimpd.mm"
include "xpopth.mm"
include "adantl.mm"
include "sylibd.mm"
include "sylbid.mm"
include "ralrimivva.mm"
include "dff1o6.mm"
include "syl3anbrc.mm"

theorem rmxypairf1o
  let cA: class A
  let va: setvar a
  let vb: setvar b
  let vc: setvar c
  let vd: setvar d

  disjoint b c
  disjoint b d
  disjoint a b
  disjoint A b
  disjoint c d
  disjoint a c
  disjoint A c
  disjoint a d
  disjoint A d
  disjoint A a
  assert |- ( A e. ( ZZ>= ` 2 ) -> ( b e. ( NN0 X. ZZ ) |-> ( ( 1st ` b ) + ( ( sqrt ` ( ( A ^ 2 ) - 1 ) ) x. ( 2nd ` b ) ) ) ) : ( NN0 X. ZZ ) -1-1-onto-> { a | E. c e. NN0 E. d e. ZZ a = ( c + ( ( sqrt ` ( ( A ^ 2 ) - 1 ) ) x. d ) ) } )

  proof
    cA
    c2
    cuz
    cfv
    wcel
    #
    vb
    cn0
    cz
    cxp
    #
    vb
    cv
    #
    c1st
    cfv
    #
    cA
    c2
    cexp
    co
    c1
    cmin
    co
    csqrt
    cfv
    #
    @2
    c2nd
    cfv
    #
    cmul
    co
    #
    caddc
    co
    #
    cmpt
    #
    @1
    wfn
    #
    @8
    crn
    #
    va
    cv
    #
    vc
    cv
    #
    @4
    vd
    cv
    #
    cmul
    co
    #
    caddc
    co
    #
    wceq
    #
    vd
    cz
    wrex
    vc
    cn0
    wrex
    #
    va
    cab
    #
    wceq
    @12
    @8
    cfv
    #
    @13
    @8
    cfv
    #
    wceq
    #
    @12
    @13
    wceq
    #
    wi
    #
    vd
    @1
    wral
    vc
    @1
    wral
    @1
    @18
    @8
    wf1o
    @9
    @0
    vb
    @1
    @7
    @8
    @3
    @6
    caddc
    ovex
    @8
    eqid
    #
    fnmpti
    a1i
    @0
    @18
    @11
    @7
    wceq
    #
    vb
    @1
    wrex
    #
    va
    cab
    @10
    @0
    @17
    @26
    va
    @17
    @26
    wb
    @0
    @26
    @17
    @25
    @16
    vb
    vc
    vd
    cn0
    cz
    @2
    @12
    @13
    cop
    wceq
    #
    @7
    @15
    @11
    @27
    @3
    @12
    @6
    @14
    caddc
    @12
    @13
    @2
    vc
    vex
    #
    vd
    vex
    #
    op1std
    @27
    @5
    @13
    @4
    cmul
    @12
    @13
    @2
    @28
    @29
    op2ndd
    oveq2d
    oveq12d
    eqeq2d
    rexxp
    bicomi
    a1i
    abbidv
    vb
    va
    @1
    @7
    @8
    @24
    rnmpt
    syl6reqr
    @0
    @23
    vc
    vd
    @1
    @1
    @0
    @12
    @1
    wcel
    #
    @13
    @1
    wcel
    #
    wa
    #
    wa
    #
    @21
    @12
    c1st
    cfv
    #
    @4
    @12
    c2nd
    cfv
    #
    cmul
    co
    #
    caddc
    co
    #
    @13
    c1st
    cfv
    #
    @4
    @13
    c2nd
    cfv
    #
    cmul
    co
    #
    caddc
    co
    #
    wceq
    #
    @22
    @33
    @19
    @37
    @20
    @41
    @30
    @19
    @37
    wceq
    @0
    @31
    vb
    @12
    @7
    @37
    @1
    @8
    @2
    @12
    wceq
    #
    @3
    @34
    @6
    @36
    caddc
    @2
    @12
    c1st
    fveq2
    @43
    @5
    @35
    @4
    cmul
    @2
    @12
    c2nd
    fveq2
    oveq2d
    oveq12d
    @24
    @34
    @36
    caddc
    ovex
    fvmpt
    ad2antrl
    @31
    @20
    @41
    wceq
    @0
    @30
    vb
    @13
    @7
    @41
    @1
    @8
    @2
    @13
    wceq
    #
    @3
    @38
    @6
    @40
    caddc
    @2
    @13
    c1st
    fveq2
    @44
    @5
    @39
    @4
    cmul
    @2
    @13
    c2nd
    fveq2
    oveq2d
    oveq12d
    @24
    @38
    @40
    caddc
    ovex
    fvmpt
    ad2antll
    eqeq12d
    @33
    @42
    @34
    @38
    wceq
    @35
    @39
    wceq
    wa
    #
    @22
    @33
    @42
    @45
    @33
    @4
    cc
    cq
    cdif
    wcel
    #
    @34
    cq
    wcel
    @35
    cq
    wcel
    #
    @38
    cq
    wcel
    @39
    cq
    wcel
    #
    @42
    @45
    wb
    @0
    @46
    @32
    cA
    rmspecsqrtnq
    adantr
    @33
    cn0
    cq
    @34
    nn0ssq
    @30
    @34
    cn0
    wcel
    @0
    @31
    @12
    cn0
    cz
    xp1st
    ad2antrl
    sseldi
    @33
    @35
    cz
    wcel
    #
    @47
    @30
    @49
    @0
    @31
    @12
    cn0
    cz
    xp2nd
    ad2antrl
    @35
    zq
    syl
    @33
    cn0
    cq
    @38
    nn0ssq
    @31
    @38
    cn0
    wcel
    @0
    @30
    @13
    cn0
    cz
    xp1st
    ad2antll
    sseldi
    @33
    @39
    cz
    wcel
    #
    @48
    @31
    @50
    @0
    @30
    @13
    cn0
    cz
    xp2nd
    ad2antll
    @39
    zq
    syl
    @4
    @34
    @35
    @38
    @39
    qirropth
    syl122anc
    biimpd
    @32
    @45
    @22
    wb
    @0
    @12
    @13
    cn0
    cz
    cn0
    cz
    xpopth
    adantl
    sylibd
    sylbid
    ralrimivva
    vc
    vd
    @1
    @18
    @8
    dff1o6
    syl3anbrc
end
