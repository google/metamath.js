include "clmod.mm"
include "wcel.mm"
include "cpw.mm"
include "wa.mm"
include "clinc.mm"
include "cfv.mm"
include "co.mm"
include "cv.mm"
include "cvsca.mm"
include "cmpt.mm"
include "cgsu.mm"
include "csca.mm"
include "cbs.mm"
include "cmap.mm"
include "wceq.mm"
include "simpl.mm"
include "wf.mm"
include "cif.mm"
include "crg.mm"
include "lmodring.mm"
include "eqcomi.mm"
include "fveq2i.mm"
include "ringidcl.mm"
include "ring0cl.mm"
include "jca.mm"
include "syl.mm"
include "ad2antrr.mm"
include "ifcl.mm"
include "fmptd.mm"
include "cvv.mm"
include "wb.mm"
include "fvex.mm"
include "a1i.mm"
include "elmapg.mm"
include "sylan.mm"
include "mpbird.mm"
include "pweqi.mm"
include "eleq2i.mm"
include "biimpi.mm"
include "adantl.mm"
include "lincval.mm"
include "syl3anc.mm"
include "simpr.mm"
include "cur.mm"
include "eqeltri.mm"
include "c0g.mm"
include "ifex.mm"
include "weq.mm"
include "eqeq1.mm"
include "ifbid.mm"
include "fvmptg.mm"
include "sylancl.mm"
include "oveq1d.mm"
include "ovif.mm"
include "oveq2.mm"
include "eqid.mm"
include "lmod1cl.mm"
include "ancli.mm"
include "adantr.mm"
include "lmodvs0.mm"
include "eqtrd.mm"
include "wn.mm"
include "wi.mm"
include "elelpwi.mm"
include "expcom.mm"
include "imp.mm"
include "lmod0vs.mm"
include "syl2anc.mm"
include "ifeqda.mm"
include "3eqtrd.mm"
include "mpteq2dva.mm"
include "oveq2d.mm"
include "cmnd.mm"
include "cgrp.mm"
include "lmodgrp.mm"
include "grpmnd.mm"
include "gsumz.mm"

theorem linc0scn0
  let vx: setvar x
  let cB: class B
  let cS: class S
  let c.1: class .1.
  let cF: class F
  let cM: class M
  let cV: class V
  let c.0: class .0.
  let cZ: class Z
  let vv: setvar v
  let vk: setvar k
  assume linc0scn0.b: |- B = ( Base ` M )
  assume linc0scn0.s: |- S = ( Scalar ` M )
  assume linc0scn0.0: |- .0. = ( 0g ` S )
  assume linc0scn0.1: |- .1. = ( 1r ` S )
  assume linc0scn0.z: |- Z = ( 0g ` M )
  assume linc0scn0.f: |- F = ( x e. V |-> if ( x = Z , .1. , .0. ) )

  disjoint B x
  disjoint M x
  disjoint V x
  disjoint Z x
  disjoint .0. x
  disjoint .1. x
  disjoint B v
  disjoint v x
  disjoint F v
  disjoint M v
  disjoint V v
  disjoint k x
  assert |- ( ( M e. LMod /\ V e. ~P B ) -> ( F ( linC ` M ) V ) = Z )

  proof
    cM
    clmod
    wcel
    #
    cV
    cB
    cpw
    #
    wcel
    #
    wa
    #
    cF
    cV
    cM
    clinc
    cfv
    co
    #
    cM
    vv
    cV
    vv
    cv
    #
    cF
    cfv
    #
    @5
    cM
    cvsca
    cfv
    #
    co
    #
    cmpt
    #
    cgsu
    co
    #
    cM
    vv
    cV
    cZ
    cmpt
    #
    cgsu
    co
    #
    cZ
    @3
    @0
    cF
    cM
    csca
    cfv
    #
    cbs
    cfv
    #
    cV
    cmap
    co
    wcel
    #
    cV
    cM
    cbs
    cfv
    #
    cpw
    #
    wcel
    #
    @4
    @10
    wceq
    @0
    @2
    simpl
    #
    @3
    @15
    cV
    @14
    cF
    wf
    #
    @3
    vx
    cV
    vx
    cv
    #
    cZ
    wceq
    #
    c.1
    c.0
    cif
    #
    @14
    cF
    @3
    @21
    cV
    wcel
    #
    wa
    c.1
    @14
    wcel
    #
    c.0
    @14
    wcel
    #
    wa
    #
    @23
    @14
    wcel
    @0
    @27
    @2
    @24
    @0
    cS
    crg
    wcel
    #
    @27
    cS
    cM
    linc0scn0.s
    lmodring
    @28
    @25
    @26
    @14
    cS
    c.1
    @13
    cS
    cbs
    cS
    @13
    linc0scn0.s
    eqcomi
    fveq2i
    #
    linc0scn0.1
    ringidcl
    @14
    cS
    c.0
    @29
    linc0scn0.0
    ring0cl
    jca
    syl
    ad2antrr
    @22
    c.1
    c.0
    @14
    ifcl
    syl
    linc0scn0.f
    fmptd
    @0
    @14
    cvv
    wcel
    #
    @2
    @15
    @20
    wb
    @30
    @0
    @13
    cbs
    fvex
    a1i
    @14
    cV
    cF
    cvv
    @1
    elmapg
    sylan
    mpbird
    @2
    @18
    @0
    @2
    @18
    @1
    @17
    cV
    cB
    @16
    linc0scn0.b
    pweqi
    eleq2i
    biimpi
    adantl
    vv
    cF
    cM
    cV
    clmod
    lincval
    syl3anc
    @3
    @9
    @11
    cM
    cgsu
    @3
    vv
    cV
    @8
    cZ
    @3
    @5
    cV
    wcel
    #
    wa
    #
    @8
    @5
    cZ
    wceq
    #
    c.1
    c.0
    cif
    #
    @5
    @7
    co
    #
    @33
    c.1
    @5
    @7
    co
    #
    c.0
    @5
    @7
    co
    #
    cif
    #
    cZ
    @32
    @6
    @34
    @5
    @7
    @32
    @31
    @34
    cvv
    wcel
    @6
    @34
    wceq
    @3
    @31
    simpr
    @33
    c.1
    c.0
    c.1
    cS
    cur
    cfv
    cvv
    linc0scn0.1
    cS
    cur
    fvex
    eqeltri
    c.0
    cS
    c0g
    cfv
    cvv
    linc0scn0.0
    cS
    c0g
    fvex
    eqeltri
    ifex
    vx
    @5
    @23
    @34
    cV
    cvv
    cF
    vx
    vv
    weq
    @22
    @33
    c.1
    c.0
    @21
    @5
    cZ
    eqeq1
    ifbid
    linc0scn0.f
    fvmptg
    sylancl
    oveq1d
    @35
    @38
    wceq
    @32
    @33
    c.1
    c.0
    @5
    @7
    ovif
    a1i
    @32
    @33
    @36
    @37
    cZ
    @32
    @33
    wa
    #
    @36
    c.1
    cZ
    @7
    co
    #
    cZ
    @33
    @36
    @40
    wceq
    @32
    @5
    cZ
    c.1
    @7
    oveq2
    adantl
    @39
    @0
    c.1
    cS
    cbs
    cfv
    #
    wcel
    #
    wa
    #
    @40
    cZ
    wceq
    @3
    @43
    @31
    @33
    @0
    @43
    @2
    @0
    @42
    c.1
    cS
    @41
    cM
    linc0scn0.s
    @41
    eqid
    #
    linc0scn0.1
    lmod1cl
    ancli
    adantr
    ad2antrr
    @7
    cS
    @41
    cM
    c.1
    cZ
    linc0scn0.s
    @7
    eqid
    #
    @44
    linc0scn0.z
    lmodvs0
    syl
    eqtrd
    @32
    @37
    cZ
    wceq
    #
    @33
    wn
    @32
    @0
    @5
    cB
    wcel
    #
    @46
    @3
    @0
    @31
    @19
    adantr
    @3
    @31
    @47
    @2
    @31
    @47
    wi
    @0
    @31
    @2
    @47
    @5
    cV
    cB
    elelpwi
    expcom
    adantl
    imp
    @7
    cS
    c.0
    cB
    cM
    @5
    cZ
    linc0scn0.b
    linc0scn0.s
    @45
    linc0scn0.0
    linc0scn0.z
    lmod0vs
    syl2anc
    adantr
    ifeqda
    3eqtrd
    mpteq2dva
    oveq2d
    @0
    cM
    cmnd
    wcel
    #
    @2
    @12
    cZ
    wceq
    @0
    cM
    cgrp
    wcel
    @48
    cM
    lmodgrp
    cM
    grpmnd
    syl
    cV
    vv
    cM
    @1
    cZ
    linc0scn0.z
    gsumz
    sylan
    3eqtrd
end
