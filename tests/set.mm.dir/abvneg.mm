include "wcel.mm"
include "wa.mm"
include "cfv.mm"
include "wceq.mm"
include "cur.mm"
include "c0g.mm"
include "crg.mm"
include "wi.mm"
include "abvrcl.mm"
include "adantr.mm"
include "cgrp.mm"
include "ringgrp.mm"
include "syl.mm"
include "grpinvcl.mm"
include "sylan.mm"
include "simpr.mm"
include "eqid.mm"
include "ring1eq0.mm"
include "syl3anc.mm"
include "imp.mm"
include "fveq2d.mm"
include "wne.mm"
include "c1.mm"
include "cmul.mm"
include "co.mm"
include "c2.mm"
include "cexp.mm"
include "cmulr.mm"
include "cr.mm"
include "ringidcl.mm"
include "syl2anc.mm"
include "abvcl.mm"
include "mpdan.mm"
include "recnd.mm"
include "sqvald.mm"
include "abvmul.mm"
include "mpd3an23.mm"
include "ringmneg2.mm"
include "ringnegl.mm"
include "grpinvinv.mm"
include "3eqtrd.mm"
include "3eqtr2d.mm"
include "abv1z.mm"
include "eqtrd.mm"
include "sq1.mm"
include "syl6eqr.mm"
include "cc0.mm"
include "cle.mm"
include "wbr.mm"
include "wb.mm"
include "abvge0.mm"
include "1re.mm"
include "0le1.mm"
include "sq11.mm"
include "mpanr12.mm"
include "biimpa.mm"
include "syldan.mm"
include "adantlr.mm"
include "oveq1d.mm"
include "simpl.mm"
include "eqtr3d.mm"
include "mulid2d.mm"
include "pm2.61dane.mm"

theorem abvneg
  let cA: class A
  let cB: class B
  let cR: class R
  let cF: class F
  let cN: class N
  let cX: class X
  assume abv0.a: |- A = ( AbsVal ` R )
  assume abvneg.b: |- B = ( Base ` R )
  assume abvneg.p: |- N = ( invg ` R )


  assert |- ( ( F e. A /\ X e. B ) -> ( F ` ( N ` X ) ) = ( F ` X ) )

  proof
    cF
    cA
    wcel
    #
    cX
    cB
    wcel
    #
    wa
    #
    cX
    cN
    cfv
    #
    cF
    cfv
    #
    cX
    cF
    cfv
    #
    wceq
    cR
    cur
    cfv
    #
    cR
    c0g
    cfv
    #
    @2
    @6
    @7
    wceq
    #
    wa
    @3
    cX
    cF
    @2
    @8
    @3
    cX
    wceq
    #
    @2
    cR
    crg
    wcel
    #
    @3
    cB
    wcel
    #
    @1
    @8
    @9
    wi
    @0
    @10
    @1
    cA
    cR
    cF
    abv0.a
    abvrcl
    #
    adantr
    #
    @0
    cR
    cgrp
    wcel
    #
    @1
    @11
    @0
    @10
    @14
    @12
    cR
    ringgrp
    syl
    #
    cB
    cR
    cN
    cX
    abvneg.b
    abvneg.p
    grpinvcl
    sylan
    @0
    @1
    simpr
    #
    cB
    cR
    @6
    @3
    cX
    @7
    abvneg.b
    @6
    eqid
    #
    @7
    eqid
    #
    ring1eq0
    syl3anc
    imp
    fveq2d
    @2
    @6
    @7
    wne
    #
    wa
    #
    c1
    @5
    cmul
    co
    #
    @4
    @5
    @20
    @6
    cN
    cfv
    #
    cF
    cfv
    #
    @5
    cmul
    co
    #
    @21
    @4
    @20
    @23
    c1
    @5
    cmul
    @0
    @19
    @23
    c1
    wceq
    #
    @1
    @0
    @19
    @23
    c2
    cexp
    co
    #
    c1
    c2
    cexp
    co
    #
    wceq
    #
    @25
    @0
    @19
    wa
    #
    @26
    c1
    @27
    @29
    @26
    @6
    cF
    cfv
    #
    c1
    @0
    @26
    @30
    wceq
    @19
    @0
    @26
    @23
    @23
    cmul
    co
    #
    @22
    @22
    cR
    cmulr
    cfv
    #
    co
    #
    cF
    cfv
    #
    @30
    @0
    @23
    @0
    @23
    @0
    @22
    cB
    wcel
    #
    @23
    cr
    wcel
    #
    @0
    @14
    @6
    cB
    wcel
    #
    @35
    @15
    @0
    @10
    @37
    @12
    cB
    cR
    @6
    abvneg.b
    @17
    ringidcl
    syl
    #
    cB
    cR
    cN
    @6
    abvneg.b
    abvneg.p
    grpinvcl
    syl2anc
    #
    cA
    cB
    cR
    cF
    @22
    abv0.a
    abvneg.b
    abvcl
    mpdan
    #
    recnd
    sqvald
    @0
    @35
    @35
    @34
    @31
    wceq
    @39
    @39
    cA
    cB
    cR
    @32
    cF
    @22
    @22
    abv0.a
    abvneg.b
    @32
    eqid
    #
    abvmul
    mpd3an23
    @0
    @33
    @6
    cF
    @0
    @33
    @22
    @6
    @32
    co
    #
    cN
    cfv
    @22
    cN
    cfv
    #
    @6
    @0
    cB
    cR
    @32
    cN
    @22
    @6
    abvneg.b
    @41
    abvneg.p
    @12
    @39
    @38
    ringmneg2
    @0
    @42
    @22
    cN
    @0
    cB
    cR
    @32
    @6
    cN
    @6
    abvneg.b
    @41
    @17
    abvneg.p
    @12
    @38
    ringnegl
    fveq2d
    @0
    @14
    @37
    @43
    @6
    wceq
    @15
    @38
    cB
    cR
    cN
    @6
    abvneg.b
    abvneg.p
    grpinvinv
    syl2anc
    3eqtrd
    fveq2d
    3eqtr2d
    adantr
    cA
    cR
    @6
    cF
    @7
    abv0.a
    @17
    @18
    abv1z
    eqtrd
    sq1
    syl6eqr
    @0
    @28
    @25
    @0
    @36
    cc0
    @23
    cle
    wbr
    #
    @28
    @25
    wb
    #
    @40
    @0
    @35
    @44
    @39
    cA
    cB
    cR
    cF
    @22
    abv0.a
    abvneg.b
    abvge0
    mpdan
    @36
    @44
    wa
    c1
    cr
    wcel
    cc0
    c1
    cle
    wbr
    @45
    1re
    0le1
    @23
    c1
    sq11
    mpanr12
    syl2anc
    biimpa
    syldan
    adantlr
    oveq1d
    @2
    @24
    @4
    wceq
    @19
    @2
    @22
    cX
    @32
    co
    #
    cF
    cfv
    #
    @24
    @4
    @2
    @0
    @35
    @1
    @47
    @24
    wceq
    @0
    @1
    simpl
    @0
    @35
    @1
    @39
    adantr
    @16
    cA
    cB
    cR
    @32
    cF
    @22
    cX
    abv0.a
    abvneg.b
    @41
    abvmul
    syl3anc
    @2
    @46
    @3
    cF
    @2
    cB
    cR
    @32
    @6
    cN
    cX
    abvneg.b
    @41
    @17
    abvneg.p
    @13
    @16
    ringnegl
    fveq2d
    eqtr3d
    adantr
    eqtr3d
    @2
    @21
    @5
    wceq
    @19
    @2
    @5
    @2
    @5
    cA
    cB
    cR
    cF
    cX
    abv0.a
    abvneg.b
    abvcl
    recnd
    mulid2d
    adantr
    eqtr3d
    pm2.61dane
end
