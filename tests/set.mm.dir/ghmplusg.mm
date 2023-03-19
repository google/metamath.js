include "cabl.mm"
include "wcel.mm"
include "cghm.mm"
include "co.mm"
include "w3a.mm"
include "cplusg.mm"
include "cfv.mm"
include "cof.mm"
include "cbs.mm"
include "eqid.mm"
include "cgrp.mm"
include "ghmgrp1.mm"
include "3ad2ant3.mm"
include "ghmgrp2.mm"
include "cvv.mm"
include "cv.mm"
include "wa.mm"
include "grpcl.mm"
include "3expb.mm"
include "sylan.mm"
include "wf.mm"
include "ghmf.mm"
include "3ad2ant2.mm"
include "fvexd.mm"
include "inidm.mm"
include "off.mm"
include "wceq.mm"
include "ghmlin.mm"
include "3ad2antl2.mm"
include "3ad2antl3.mm"
include "oveq12d.mm"
include "ccmn.mm"
include "simpl1.mm"
include "ablcmn.mm"
include "syl.mm"
include "ffvelrnda.mm"
include "adantrr.mm"
include "adantrl.mm"
include "cmn4.mm"
include "syl122anc.mm"
include "eqtrd.mm"
include "wfn.mm"
include "ffn.mm"
include "adantr.mm"
include "fnfvof.mm"
include "syl22anc.mm"
include "simprl.mm"
include "simprr.mm"
include "3eqtr4d.mm"
include "isghmd.mm"

theorem ghmplusg
  let c.pl: class .+
  let cF: class F
  let cG: class G
  let cM: class M
  let cN: class N
  let vx: setvar x
  let vy: setvar y
  assume ghmplusg.p: |- .+ = ( +g ` N )


  assert |- ( ( N e. Abel /\ F e. ( M GrpHom N ) /\ G e. ( M GrpHom N ) ) -> ( F oF .+ G ) e. ( M GrpHom N ) )

  proof
    cN
    cabl
    wcel
    #
    cF
    cM
    cN
    cghm
    co
    #
    wcel
    #
    cG
    @1
    wcel
    #
    w3a
    #
    vx
    vy
    cM
    cplusg
    cfv
    #
    c.pl
    cM
    cN
    cF
    cG
    c.pl
    cof
    co
    #
    cM
    cbs
    cfv
    #
    cN
    cbs
    cfv
    #
    @7
    eqid
    #
    @8
    eqid
    #
    @5
    eqid
    #
    ghmplusg.p
    @3
    @0
    cM
    cgrp
    wcel
    #
    @2
    cM
    cN
    cG
    ghmgrp1
    3ad2ant3
    #
    @3
    @0
    cN
    cgrp
    wcel
    #
    @2
    cM
    cN
    cG
    ghmgrp2
    3ad2ant3
    #
    @4
    vx
    vy
    @7
    @7
    @7
    c.pl
    @8
    @8
    @8
    cF
    cG
    cvv
    cvv
    @4
    @14
    vx
    cv
    #
    @8
    wcel
    #
    vy
    cv
    #
    @8
    wcel
    #
    wa
    @16
    @18
    c.pl
    co
    @8
    wcel
    #
    @15
    @14
    @17
    @19
    @20
    @8
    c.pl
    cN
    @16
    @18
    @10
    ghmplusg.p
    grpcl
    3expb
    sylan
    @2
    @0
    @7
    @8
    cF
    wf
    #
    @3
    cM
    cN
    cF
    @7
    @8
    @9
    @10
    ghmf
    3ad2ant2
    #
    @3
    @0
    @7
    @8
    cG
    wf
    #
    @2
    cM
    cN
    cG
    @7
    @8
    @9
    @10
    ghmf
    3ad2ant3
    #
    @4
    cM
    cbs
    fvexd
    #
    @25
    @7
    inidm
    off
    @4
    @16
    @7
    wcel
    #
    @18
    @7
    wcel
    #
    wa
    #
    wa
    #
    @16
    @18
    @5
    co
    #
    cF
    cfv
    #
    @30
    cG
    cfv
    #
    c.pl
    co
    #
    @16
    cF
    cfv
    #
    @16
    cG
    cfv
    #
    c.pl
    co
    #
    @18
    cF
    cfv
    #
    @18
    cG
    cfv
    #
    c.pl
    co
    #
    c.pl
    co
    #
    @30
    @6
    cfv
    #
    @16
    @6
    cfv
    #
    @18
    @6
    cfv
    #
    c.pl
    co
    @29
    @33
    @34
    @37
    c.pl
    co
    #
    @35
    @38
    c.pl
    co
    #
    c.pl
    co
    #
    @40
    @29
    @31
    @44
    @32
    @45
    c.pl
    @2
    @0
    @28
    @31
    @44
    wceq
    #
    @3
    @2
    @26
    @27
    @47
    @5
    c.pl
    cM
    cN
    @16
    cF
    @18
    @7
    @9
    @11
    ghmplusg.p
    ghmlin
    3expb
    3ad2antl2
    @3
    @0
    @28
    @32
    @45
    wceq
    #
    @2
    @3
    @26
    @27
    @48
    @5
    c.pl
    cM
    cN
    @16
    cG
    @18
    @7
    @9
    @11
    ghmplusg.p
    ghmlin
    3expb
    3ad2antl3
    oveq12d
    @29
    cN
    ccmn
    wcel
    #
    @34
    @8
    wcel
    #
    @37
    @8
    wcel
    #
    @35
    @8
    wcel
    #
    @38
    @8
    wcel
    #
    @46
    @40
    wceq
    @29
    @0
    @49
    @0
    @2
    @3
    @28
    simpl1
    cN
    ablcmn
    syl
    @4
    @26
    @50
    @27
    @4
    @7
    @8
    @16
    cF
    @22
    ffvelrnda
    adantrr
    @4
    @27
    @51
    @26
    @4
    @7
    @8
    @18
    cF
    @22
    ffvelrnda
    adantrl
    @4
    @26
    @52
    @27
    @4
    @7
    @8
    @16
    cG
    @24
    ffvelrnda
    adantrr
    @4
    @27
    @53
    @26
    @4
    @7
    @8
    @18
    cG
    @24
    ffvelrnda
    adantrl
    @8
    c.pl
    cN
    @38
    @34
    @37
    @35
    @10
    ghmplusg.p
    cmn4
    syl122anc
    eqtrd
    @29
    cF
    @7
    wfn
    #
    cG
    @7
    wfn
    #
    @7
    cvv
    wcel
    #
    @30
    @7
    wcel
    #
    @41
    @33
    wceq
    @4
    @54
    @28
    @4
    @21
    @54
    @22
    @7
    @8
    cF
    ffn
    syl
    adantr
    #
    @4
    @55
    @28
    @4
    @23
    @55
    @24
    @7
    @8
    cG
    ffn
    syl
    adantr
    #
    @29
    cM
    cbs
    fvexd
    #
    @4
    @12
    @28
    @57
    @13
    @12
    @26
    @27
    @57
    @7
    @5
    cM
    @16
    @18
    @9
    @11
    grpcl
    3expb
    sylan
    @7
    c.pl
    cF
    cG
    cvv
    @30
    fnfvof
    syl22anc
    @29
    @42
    @36
    @43
    @39
    c.pl
    @29
    @54
    @55
    @56
    @26
    @42
    @36
    wceq
    @58
    @59
    @60
    @4
    @26
    @27
    simprl
    @7
    c.pl
    cF
    cG
    cvv
    @16
    fnfvof
    syl22anc
    @29
    @54
    @55
    @56
    @27
    @43
    @39
    wceq
    @58
    @59
    @60
    @4
    @26
    @27
    simprr
    @7
    c.pl
    cF
    cG
    cvv
    @18
    fnfvof
    syl22anc
    oveq12d
    3eqtr4d
    isghmd
end
