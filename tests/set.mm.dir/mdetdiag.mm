include "ccrg.mm"
include "wcel.mm"
include "cfn.mm"
include "w3a.mm"
include "cv.mm"
include "wne.mm"
include "co.mm"
include "wceq.mm"
include "wi.mm"
include "wral.mm"
include "cfv.mm"
include "cmpt.mm"
include "cgsu.mm"
include "wa.mm"
include "csymg.mm"
include "cbs.mm"
include "czrh.mm"
include "cpsgn.mm"
include "ccom.mm"
include "cmulr.mm"
include "cid.mm"
include "cres.mm"
include "cif.mm"
include "simpl3.mm"
include "eqid.mm"
include "mdetleib.mm"
include "syl.mm"
include "simpl1.mm"
include "ad2antrr.mm"
include "simpr.mm"
include "madetsumid.mm"
include "syl3anc.mm"
include "iftrue.mm"
include "eqcomd.mm"
include "adantl.mm"
include "eqtrd.mm"
include "wn.mm"
include "simplll.mm"
include "df-ne.mm"
include "biimpri.mm"
include "anim12i.mm"
include "mdetdiaglem.mm"
include "iffalse.mm"
include "pm2.61dan.mm"
include "mpteq2dva.mm"
include "oveq2d.mm"
include "cvv.mm"
include "cmnd.mm"
include "crg.mm"
include "crngring.mm"
include "ringmnd.mm"
include "3ad2ant1.mm"
include "adantr.mm"
include "fvexd.mm"
include "c0g.mm"
include "symgid.mm"
include "3ad2ant2.mm"
include "cgrp.mm"
include "symggrp.mm"
include "grpidcl.mm"
include "eqeltrd.mm"
include "mgpbas.mm"
include "ccmn.mm"
include "crngmgp.mm"
include "simpl2.mm"
include "eleq2i.mm"
include "biimpi.mm"
include "3ad2ant3.mm"
include "matecl.mm"
include "ralrimiva.mm"
include "gsummptcl.mm"
include "gsummptif1n0.mm"
include "3eqtrd.mm"
include "ex.mm"

theorem mdetdiag
  let cA: class A
  let cB: class B
  let cD: class D
  let cR: class R
  let vi: setvar i
  let vj: setvar j
  let vk: setvar k
  let cG: class G
  let cM: class M
  let cN: class N
  let c.0: class .0.
  let vp: setvar p
  assume mdetdiag.d: |- D = ( N maDet R )
  assume mdetdiag.a: |- A = ( N Mat R )
  assume mdetdiag.b: |- B = ( Base ` A )
  assume mdetdiag.g: |- G = ( mulGrp ` R )
  assume mdetdiag.0: |- .0. = ( 0g ` R )

  disjoint B k
  disjoint G k
  disjoint M i
  disjoint M j
  disjoint M k
  disjoint i j
  disjoint i k
  disjoint j k
  disjoint N i
  disjoint N j
  disjoint N k
  disjoint R k
  disjoint .0. i
  disjoint .0. j
  disjoint .0. k
  disjoint B p
  disjoint k p
  disjoint G p
  disjoint M p
  disjoint i p
  disjoint j p
  disjoint N p
  disjoint R p
  disjoint .0. p
  assert |- ( ( R e. CRing /\ N e. Fin /\ M e. B ) -> ( A. i e. N A. j e. N ( i =/= j -> ( i M j ) = .0. ) -> ( D ` M ) = ( G gsum ( k e. N |-> ( k M k ) ) ) ) )

  proof
    cR
    ccrg
    wcel
    #
    cN
    cfn
    wcel
    #
    cM
    cB
    wcel
    #
    w3a
    #
    vi
    cv
    #
    vj
    cv
    #
    wne
    @4
    @5
    cM
    co
    c.0
    wceq
    wi
    vj
    cN
    wral
    vi
    cN
    wral
    #
    cM
    cD
    cfv
    #
    cG
    vk
    cN
    vk
    cv
    #
    @8
    cM
    co
    #
    cmpt
    cgsu
    co
    #
    wceq
    @3
    @6
    wa
    #
    @7
    cR
    vp
    cN
    csymg
    cfv
    #
    cbs
    cfv
    #
    vp
    cv
    #
    cR
    czrh
    cfv
    #
    cN
    cpsgn
    cfv
    #
    ccom
    cfv
    cG
    vk
    cN
    @8
    @14
    cfv
    @8
    cM
    co
    cmpt
    cgsu
    co
    cR
    cmulr
    cfv
    #
    co
    #
    cmpt
    #
    cgsu
    co
    #
    cR
    vp
    @13
    @14
    cid
    cN
    cres
    #
    wceq
    #
    @10
    c.0
    cif
    #
    cmpt
    #
    cgsu
    co
    @10
    @11
    @2
    @7
    @20
    wceq
    @0
    @1
    @2
    @6
    simpl3
    #
    vk
    cA
    cB
    cD
    @13
    cR
    @16
    @17
    cG
    cM
    cN
    @15
    vp
    mdetdiag.d
    mdetdiag.a
    mdetdiag.b
    @13
    eqid
    #
    @15
    eqid
    #
    @16
    eqid
    #
    @17
    eqid
    #
    mdetdiag.g
    mdetleib
    syl
    @11
    @19
    @24
    cR
    cgsu
    @11
    vp
    @13
    @18
    @23
    @11
    @14
    @13
    wcel
    #
    wa
    #
    @22
    @18
    @23
    wceq
    @31
    @22
    wa
    #
    @18
    @10
    @23
    @32
    @0
    @2
    @22
    @18
    @10
    wceq
    @11
    @0
    @30
    @22
    @0
    @1
    @2
    @6
    simpl1
    ad2antrr
    @11
    @2
    @30
    @22
    @25
    ad2antrr
    @31
    @22
    simpr
    cA
    cB
    @14
    cR
    @16
    @17
    cG
    cM
    cN
    @15
    vk
    mdetdiag.a
    mdetdiag.b
    mdetdiag.g
    @27
    @28
    @29
    madetsumid
    syl3anc
    @22
    @10
    @23
    wceq
    @31
    @22
    @23
    @10
    @22
    @10
    c.0
    iftrue
    eqcomd
    adantl
    eqtrd
    @31
    @22
    wn
    #
    wa
    #
    @18
    c.0
    @23
    @34
    @3
    @6
    @30
    @14
    @21
    wne
    #
    wa
    @18
    c.0
    wceq
    @3
    @6
    @30
    @33
    simplll
    @11
    @6
    @30
    @33
    @3
    @6
    simpr
    ad2antrr
    @31
    @30
    @33
    @35
    @11
    @30
    simpr
    @35
    @33
    @14
    @21
    df-ne
    biimpri
    anim12i
    cA
    cB
    cD
    @14
    cR
    @16
    @17
    vi
    vj
    vk
    cG
    @13
    cM
    cN
    c.0
    @15
    mdetdiag.d
    mdetdiag.a
    mdetdiag.b
    mdetdiag.g
    mdetdiag.0
    @26
    @27
    @28
    @29
    mdetdiaglem
    syl3anc
    @34
    @23
    c.0
    @33
    @23
    c.0
    wceq
    @31
    @22
    @10
    c.0
    iffalse
    adantl
    eqcomd
    eqtrd
    pm2.61dan
    mpteq2dva
    oveq2d
    @11
    @10
    vp
    @24
    cR
    @13
    cvv
    @21
    c.0
    mdetdiag.0
    @3
    cR
    cmnd
    wcel
    #
    @6
    @0
    @1
    @36
    @2
    @0
    cR
    crg
    wcel
    @36
    cR
    crngring
    cR
    ringmnd
    syl
    3ad2ant1
    adantr
    @11
    @12
    cbs
    fvexd
    @3
    @21
    @13
    wcel
    @6
    @3
    @21
    @12
    c0g
    cfv
    #
    @13
    @1
    @0
    @21
    @37
    wceq
    @2
    cN
    @12
    cfn
    @12
    eqid
    #
    symgid
    3ad2ant2
    @3
    @12
    cgrp
    wcel
    #
    @37
    @13
    wcel
    @1
    @0
    @39
    @2
    cN
    @12
    cfn
    @38
    symggrp
    3ad2ant2
    @13
    @12
    @37
    @26
    @37
    eqid
    grpidcl
    syl
    eqeltrd
    adantr
    @24
    eqid
    @11
    cR
    cbs
    cfv
    #
    vk
    cG
    cN
    @9
    @40
    cR
    cG
    mdetdiag.g
    @40
    eqid
    #
    mgpbas
    @3
    cG
    ccmn
    wcel
    #
    @6
    @0
    @1
    @42
    @2
    cR
    cG
    mdetdiag.g
    crngmgp
    3ad2ant1
    adantr
    @0
    @1
    @2
    @6
    simpl2
    @11
    @9
    @40
    wcel
    #
    vk
    cN
    @11
    @8
    cN
    wcel
    #
    wa
    @44
    @44
    cM
    cA
    cbs
    cfv
    #
    wcel
    #
    @43
    @11
    @44
    simpr
    #
    @47
    @3
    @46
    @6
    @44
    @2
    @0
    @46
    @1
    @2
    @46
    cB
    @45
    cM
    mdetdiag.b
    eleq2i
    biimpi
    3ad2ant3
    ad2antrr
    cA
    cR
    @8
    @8
    @40
    cM
    cN
    mdetdiag.a
    @41
    matecl
    syl3anc
    ralrimiva
    gsummptcl
    gsummptif1n0
    3eqtrd
    ex
end
