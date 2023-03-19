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
include "eqcomi.mm"
include "fveq2i.mm"
include "lmod0cl.mm"
include "adantr.mm"
include "fmptd.mm"
include "cvv.mm"
include "wb.mm"
include "fvexd.mm"
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
include "c0g.mm"
include "fvex.mm"
include "eqeltri.mm"
include "weq.mm"
include "eqidd.mm"
include "fvmptg.mm"
include "sylancl.mm"
include "oveq1d.mm"
include "wi.mm"
include "elelpwi.mm"
include "expcom.mm"
include "imp.mm"
include "eqid.mm"
include "lmod0vs.mm"
include "syl2anc.mm"
include "eqtrd.mm"
include "mpteq2dva.mm"
include "oveq2d.mm"
include "cmnd.mm"
include "cgrp.mm"
include "lmodgrp.mm"
include "grpmnd.mm"
include "syl.mm"
include "gsumz.mm"
include "3eqtrd.mm"

theorem lincvalsc0
  let vx: setvar x
  let cB: class B
  let cS: class S
  let cF: class F
  let cM: class M
  let cV: class V
  let c.0: class .0.
  let cZ: class Z
  let vv: setvar v
  let vk: setvar k
  assume lincvalsc0.b: |- B = ( Base ` M )
  assume lincvalsc0.s: |- S = ( Scalar ` M )
  assume lincvalsc0.0: |- .0. = ( 0g ` S )
  assume lincvalsc0.z: |- Z = ( 0g ` M )
  assume lincvalsc0.f: |- F = ( x e. V |-> .0. )

  disjoint B x
  disjoint M x
  disjoint V x
  disjoint .0. x
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
    c.0
    @14
    cF
    @3
    c.0
    @14
    wcel
    #
    vx
    cv
    cV
    wcel
    @0
    @21
    @2
    cS
    @14
    cM
    c.0
    lincvalsc0.s
    @13
    cS
    cbs
    cS
    @13
    lincvalsc0.s
    eqcomi
    fveq2i
    lincvalsc0.0
    lmod0cl
    adantr
    adantr
    lincvalsc0.f
    fmptd
    @0
    @14
    cvv
    wcel
    @2
    @15
    @20
    wb
    @0
    @13
    cbs
    fvexd
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
    lincvalsc0.b
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
    c.0
    @5
    @7
    co
    #
    cZ
    @23
    @6
    c.0
    @5
    @7
    @23
    @22
    c.0
    cvv
    wcel
    @6
    c.0
    wceq
    @3
    @22
    simpr
    c.0
    cS
    c0g
    cfv
    cvv
    lincvalsc0.0
    cS
    c0g
    fvex
    eqeltri
    vx
    @5
    c.0
    c.0
    cV
    cvv
    cF
    vx
    vv
    weq
    c.0
    eqidd
    lincvalsc0.f
    fvmptg
    sylancl
    oveq1d
    @23
    @0
    @5
    cB
    wcel
    #
    @24
    cZ
    wceq
    @3
    @0
    @22
    @19
    adantr
    @3
    @22
    @25
    @2
    @22
    @25
    wi
    @0
    @22
    @2
    @25
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
    lincvalsc0.b
    lincvalsc0.s
    @7
    eqid
    lincvalsc0.0
    lincvalsc0.z
    lmod0vs
    syl2anc
    eqtrd
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
    @26
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
    lincvalsc0.z
    gsumz
    sylan
    3eqtrd
end
