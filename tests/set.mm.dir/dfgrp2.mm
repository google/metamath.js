include "cgrp.mm"
include "wcel.mm"
include "csgrp.mm"
include "cv.mm"
include "co.mm"
include "wceq.mm"
include "wrex.mm"
include "wa.mm"
include "wral.mm"
include "grpsgrp.mm"
include "c0g.mm"
include "cfv.mm"
include "cmnd.mm"
include "grpmnd.mm"
include "eqid.mm"
include "mndidcl.mm"
include "syl.mm"
include "wb.mm"
include "oveq1.mm"
include "eqeq1d.mm"
include "eqeq2.mm"
include "rexbidv.mm"
include "anbi12d.mm"
include "ralbidv.mm"
include "adantl.mm"
include "mndlid.mm"
include "sylan.mm"
include "grpinvex.mm"
include "jca.mm"
include "ralrimiva.mm"
include "rspcedvd.mm"
include "wi.mm"
include "cbs.mm"
include "a1i.mm"
include "cplusg.mm"
include "cmgm.mm"
include "sgrpmgm.mm"
include "mgmcl.mm"
include "syl3an1.mm"
include "w3a.mm"
include "sgrpass.mm"
include "adantll.mm"
include "simpll.mm"
include "oveq2.mm"
include "id.mm"
include "eqeq12d.mm"
include "rspcv.mm"
include "simpl.mm"
include "syl6com.mm"
include "ad2antlr.mm"
include "imp.mm"
include "cbvrexv.mm"
include "biimpi.mm"
include "isgrpde.mm"
include "ex.mm"
include "rexlimiva.mm"
include "impcom.mm"
include "impbii.mm"

theorem dfgrp2
  let vx: setvar x
  let cB: class B
  let c.pl: class .+
  let vi: setvar i
  let vn: setvar n
  let cG: class G
  let va: setvar a
  let vb: setvar b
  let vc: setvar c
  assume dfgrp2.b: |- B = ( Base ` G )
  assume dfgrp2.p: |- .+ = ( +g ` G )

  disjoint B i
  disjoint B n
  disjoint B x
  disjoint i n
  disjoint i x
  disjoint n x
  disjoint G i
  disjoint G n
  disjoint G x
  disjoint .+ i
  disjoint .+ n
  disjoint .+ x
  disjoint B a
  disjoint B b
  disjoint B c
  disjoint a b
  disjoint a c
  disjoint a i
  disjoint a n
  disjoint a x
  disjoint b c
  disjoint b i
  disjoint b n
  disjoint b x
  disjoint c i
  disjoint c n
  disjoint c x
  disjoint G a
  disjoint G b
  disjoint G c
  disjoint .+ a
  disjoint .+ b
  disjoint .+ c
  assert |- ( G e. Grp <-> ( G e. SGrp /\ E. n e. B A. x e. B ( ( n .+ x ) = x /\ E. i e. B ( i .+ x ) = n ) ) )

  proof
    cG
    cgrp
    wcel
    #
    cG
    csgrp
    wcel
    #
    vn
    cv
    #
    vx
    cv
    #
    c.pl
    co
    #
    @3
    wceq
    #
    vi
    cv
    #
    @3
    c.pl
    co
    #
    @2
    wceq
    #
    vi
    cB
    wrex
    #
    wa
    #
    vx
    cB
    wral
    #
    vn
    cB
    wrex
    #
    wa
    @0
    @1
    @12
    cG
    grpsgrp
    @0
    @11
    cG
    c0g
    cfv
    #
    @3
    c.pl
    co
    #
    @3
    wceq
    #
    @7
    @13
    wceq
    #
    vi
    cB
    wrex
    #
    wa
    #
    vx
    cB
    wral
    #
    vn
    @13
    cB
    @0
    cG
    cmnd
    wcel
    #
    @13
    cB
    wcel
    cG
    grpmnd
    #
    cB
    cG
    @13
    dfgrp2.b
    @13
    eqid
    #
    mndidcl
    syl
    @2
    @13
    wceq
    #
    @11
    @19
    wb
    @0
    @23
    @10
    @18
    vx
    cB
    @23
    @5
    @15
    @9
    @17
    @23
    @4
    @14
    @3
    @2
    @13
    @3
    c.pl
    oveq1
    eqeq1d
    @23
    @8
    @16
    vi
    cB
    @2
    @13
    @7
    eqeq2
    rexbidv
    anbi12d
    ralbidv
    adantl
    @0
    @18
    vx
    cB
    @0
    @3
    cB
    wcel
    #
    wa
    @15
    @17
    @0
    @20
    @24
    @15
    @21
    cB
    c.pl
    cG
    @3
    @13
    dfgrp2.b
    dfgrp2.p
    @22
    mndlid
    sylan
    vi
    cB
    c.pl
    cG
    @3
    @13
    dfgrp2.b
    dfgrp2.p
    @22
    grpinvex
    jca
    ralrimiva
    rspcedvd
    jca
    @12
    @1
    @0
    @11
    @1
    @0
    wi
    vn
    cB
    @2
    cB
    wcel
    #
    @11
    wa
    #
    @1
    @0
    @26
    @1
    wa
    #
    va
    vb
    vc
    cB
    c.pl
    cG
    @2
    cB
    cG
    cbs
    cfv
    wceq
    @27
    dfgrp2.b
    a1i
    c.pl
    cG
    cplusg
    cfv
    wceq
    @27
    dfgrp2.p
    a1i
    @27
    cG
    cmgm
    wcel
    #
    va
    cv
    #
    cB
    wcel
    #
    vb
    cv
    #
    cB
    wcel
    #
    @29
    @31
    c.pl
    co
    #
    cB
    wcel
    @1
    @28
    @26
    cG
    sgrpmgm
    adantl
    cB
    cG
    @29
    @31
    c.pl
    dfgrp2.b
    dfgrp2.p
    mgmcl
    syl3an1
    @1
    @30
    @32
    vc
    cv
    #
    cB
    wcel
    w3a
    @33
    @34
    c.pl
    co
    @29
    @31
    @34
    c.pl
    co
    c.pl
    co
    wceq
    @26
    cB
    cG
    @29
    @31
    c.pl
    @34
    dfgrp2.b
    dfgrp2.p
    sgrpass
    adantll
    @25
    @11
    @1
    simpll
    @27
    @30
    @2
    @29
    c.pl
    co
    #
    @29
    wceq
    #
    @11
    @30
    @36
    wi
    @25
    @1
    @30
    @11
    @36
    @6
    @29
    c.pl
    co
    #
    @2
    wceq
    #
    vi
    cB
    wrex
    #
    wa
    #
    @36
    @10
    @40
    vx
    @29
    cB
    @3
    @29
    wceq
    #
    @5
    @36
    @9
    @39
    @41
    @4
    @35
    @3
    @29
    @3
    @29
    @2
    c.pl
    oveq2
    @41
    id
    eqeq12d
    @41
    @8
    @38
    vi
    cB
    @41
    @7
    @37
    @2
    @3
    @29
    @6
    c.pl
    oveq2
    eqeq1d
    rexbidv
    anbi12d
    rspcv
    #
    @36
    @39
    simpl
    syl6com
    ad2antlr
    imp
    @27
    @30
    @31
    @29
    c.pl
    co
    #
    @2
    wceq
    #
    vb
    cB
    wrex
    #
    @11
    @30
    @45
    wi
    @25
    @1
    @30
    @11
    @40
    @45
    @42
    @39
    @45
    @36
    @39
    @45
    @38
    @44
    vi
    vb
    cB
    @6
    @31
    wceq
    @37
    @43
    @2
    @6
    @31
    @29
    c.pl
    oveq1
    eqeq1d
    cbvrexv
    biimpi
    adantl
    syl6com
    ad2antlr
    imp
    isgrpde
    ex
    rexlimiva
    impcom
    impbii
end
