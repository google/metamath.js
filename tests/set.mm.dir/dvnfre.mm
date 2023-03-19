include "cr.mm"
include "wf.mm"
include "wss.mm"
include "cn0.mm"
include "wcel.mm"
include "cdvn.mm"
include "co.mm"
include "cfv.mm"
include "cdm.mm"
include "wa.mm"
include "cv.mm"
include "wi.mm"
include "cc0.mm"
include "c1.mm"
include "caddc.mm"
include "wceq.mm"
include "fveq2.mm"
include "dmeqd.mm"
include "feq12d.mm"
include "imbi2d.mm"
include "simpl.mm"
include "cc.mm"
include "cpm.mm"
include "ax-resscn.mm"
include "fss.mm"
include "mpan2.mm"
include "cvv.mm"
include "cnex.mm"
include "reex.mm"
include "elpm2r.mm"
include "mpanl12.mm"
include "sylan.mm"
include "dvn0.mm"
include "sylancr.mm"
include "fdm.mm"
include "adantr.mm"
include "eqtrd.mm"
include "mpbird.mm"
include "cdv.mm"
include "simprr.mm"
include "cpr.mm"
include "prid1.mm"
include "a1i.mm"
include "simprl.mm"
include "dvnbss.mm"
include "syl3anc.mm"
include "sseqtrd.mm"
include "simplr.mm"
include "sstrd.mm"
include "dvfre.mm"
include "syl2anc.mm"
include "dvnp1.mm"
include "expr.mm"
include "expcom.mm"
include "a2d.mm"
include "nn0ind.mm"
include "com12.mm"
include "3impia.mm"

theorem dvnfre
  let cA: class A
  let cF: class F
  let cN: class N
  let vn: setvar n
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z


  assert |- ( ( F : A --> RR /\ A C_ RR /\ N e. NN0 ) -> ( ( RR Dn F ) ` N ) : dom ( ( RR Dn F ) ` N ) --> RR )

  proof
    cA
    cr
    cF
    wf
    #
    cA
    cr
    wss
    #
    cN
    cn0
    wcel
    #
    cN
    cr
    cF
    cdvn
    co
    #
    cfv
    #
    cdm
    #
    cr
    @4
    wf
    #
    @2
    @0
    @1
    wa
    #
    @6
    @7
    vx
    cv
    #
    @3
    cfv
    #
    cdm
    #
    cr
    @9
    wf
    #
    wi
    @7
    cc0
    @3
    cfv
    #
    cdm
    #
    cr
    @12
    wf
    #
    wi
    @7
    vn
    cv
    #
    @3
    cfv
    #
    cdm
    #
    cr
    @16
    wf
    #
    wi
    @7
    @15
    c1
    caddc
    co
    #
    @3
    cfv
    #
    cdm
    #
    cr
    @20
    wf
    #
    wi
    @7
    @6
    wi
    vx
    vn
    cN
    @8
    cc0
    wceq
    #
    @11
    @14
    @7
    @23
    @10
    @13
    cr
    @9
    @12
    @8
    cc0
    @3
    fveq2
    #
    @23
    @9
    @12
    @24
    dmeqd
    feq12d
    imbi2d
    @8
    @15
    wceq
    #
    @11
    @18
    @7
    @25
    @10
    @17
    cr
    @9
    @16
    @8
    @15
    @3
    fveq2
    #
    @25
    @9
    @16
    @26
    dmeqd
    feq12d
    imbi2d
    @8
    @19
    wceq
    #
    @11
    @22
    @7
    @27
    @10
    @21
    cr
    @9
    @20
    @8
    @19
    @3
    fveq2
    #
    @27
    @9
    @20
    @28
    dmeqd
    feq12d
    imbi2d
    @8
    cN
    wceq
    #
    @11
    @6
    @7
    @29
    @10
    @5
    cr
    @9
    @4
    @8
    cN
    @3
    fveq2
    #
    @29
    @9
    @4
    @30
    dmeqd
    feq12d
    imbi2d
    @7
    @14
    @0
    @0
    @1
    simpl
    @7
    @13
    cA
    cr
    @12
    cF
    @7
    cr
    cc
    wss
    #
    cF
    cc
    cr
    cpm
    co
    wcel
    #
    @12
    cF
    wceq
    ax-resscn
    @0
    cA
    cc
    cF
    wf
    #
    @1
    @32
    @0
    @31
    @33
    ax-resscn
    cA
    cr
    cc
    cF
    fss
    mpan2
    cc
    cvv
    wcel
    cr
    cvv
    wcel
    @33
    @1
    wa
    @32
    cnex
    reex
    cc
    cr
    cA
    cF
    cvv
    cvv
    elpm2r
    mpanl12
    sylan
    #
    cr
    cF
    dvn0
    sylancr
    #
    @7
    @13
    cF
    cdm
    #
    cA
    @7
    @12
    cF
    @35
    dmeqd
    @0
    @36
    cA
    wceq
    #
    @1
    cA
    cr
    cF
    fdm
    adantr
    #
    eqtrd
    feq12d
    mpbird
    @15
    cn0
    wcel
    #
    @7
    @18
    @22
    @7
    @39
    @18
    @22
    wi
    @7
    @39
    @18
    @22
    @7
    @39
    @18
    wa
    #
    wa
    #
    @22
    cr
    @16
    cdv
    co
    #
    cdm
    #
    cr
    @42
    wf
    #
    @41
    @18
    @17
    cr
    wss
    @44
    @7
    @39
    @18
    simprr
    @41
    @17
    cA
    cr
    @41
    @17
    @36
    cA
    @41
    cr
    cr
    cc
    cpr
    wcel
    #
    @32
    @39
    @17
    @36
    wss
    @45
    @41
    cr
    cc
    reex
    prid1
    a1i
    @7
    @32
    @40
    @34
    adantr
    #
    @7
    @39
    @18
    simprl
    #
    cr
    cF
    @15
    dvnbss
    syl3anc
    @7
    @37
    @40
    @38
    adantr
    sseqtrd
    @0
    @1
    @40
    simplr
    sstrd
    @17
    @16
    dvfre
    syl2anc
    @41
    @21
    @43
    cr
    @20
    @42
    @41
    @31
    @32
    @39
    @20
    @42
    wceq
    @31
    @41
    ax-resscn
    a1i
    @46
    @47
    cr
    cF
    @15
    dvnp1
    syl3anc
    #
    @41
    @20
    @42
    @48
    dmeqd
    feq12d
    mpbird
    expr
    expcom
    a2d
    nn0ind
    com12
    3impia
end
