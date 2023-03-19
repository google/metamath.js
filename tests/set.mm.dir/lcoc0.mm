include "clmod.mm"
include "wcel.mm"
include "cpw.mm"
include "wa.mm"
include "cmap.mm"
include "co.mm"
include "cfsupp.mm"
include "wbr.mm"
include "clinc.mm"
include "cfv.mm"
include "wceq.mm"
include "wf.mm"
include "cv.mm"
include "lmod0cl.mm"
include "ad2antrr.mm"
include "fmptd.mm"
include "cvv.mm"
include "wb.mm"
include "cbs.mm"
include "fvex.mm"
include "eqeltri.mm"
include "a1i.mm"
include "elmapg.mm"
include "sylan.mm"
include "mpbird.mm"
include "csupp.mm"
include "cfn.mm"
include "wne.mm"
include "crab.mm"
include "cmpt.mm"
include "weq.mm"
include "eqidd.mm"
include "cbvmptv.mm"
include "eqtri.mm"
include "simpr.mm"
include "c0g.mm"
include "mptsuppd.mm"
include "c0.mm"
include "wn.mm"
include "wral.mm"
include "neirr.mm"
include "ralrimivw.mm"
include "rabeq0.mm"
include "sylibr.mm"
include "0fin.mm"
include "eqeltrd.mm"
include "wfun.mm"
include "funmpt2.mm"
include "funisfsupp.mm"
include "syl3anc.mm"
include "lincvalsc0.mm"
include "3jca.mm"

theorem lcoc0
  let vx: setvar x
  let cB: class B
  let cR: class R
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
  assume lcoc0.r: |- R = ( Base ` S )

  disjoint B x
  disjoint M x
  disjoint V x
  disjoint .0. x
  disjoint F x
  disjoint R x
  disjoint B v
  disjoint v x
  disjoint F v
  disjoint M v
  disjoint V v
  disjoint .0. v
  disjoint k x
  assert |- ( ( M e. LMod /\ V e. ~P B ) -> ( F e. ( R ^m V ) /\ F finSupp .0. /\ ( F ( linC ` M ) V ) = Z ) )

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
    cR
    cV
    cmap
    co
    #
    wcel
    #
    cF
    c.0
    cfsupp
    wbr
    #
    cF
    cV
    cM
    clinc
    cfv
    co
    cZ
    wceq
    @3
    @5
    cV
    cR
    cF
    wf
    #
    @3
    vx
    cV
    c.0
    cR
    cF
    @0
    c.0
    cR
    wcel
    @2
    vx
    cv
    cV
    wcel
    cS
    cR
    cM
    c.0
    lincvalsc0.s
    lcoc0.r
    lincvalsc0.0
    lmod0cl
    ad2antrr
    lincvalsc0.f
    fmptd
    @0
    cR
    cvv
    wcel
    #
    @2
    @5
    @7
    wb
    @8
    @0
    cR
    cS
    cbs
    cfv
    cvv
    lcoc0.r
    cS
    cbs
    fvex
    eqeltri
    a1i
    cR
    cV
    cF
    cvv
    @1
    elmapg
    sylan
    mpbird
    #
    @3
    @6
    cF
    c.0
    csupp
    co
    #
    cfn
    wcel
    #
    @3
    @10
    c.0
    c.0
    wne
    #
    vv
    cV
    crab
    #
    cfn
    @3
    vv
    cV
    c.0
    cvv
    cF
    @1
    cvv
    c.0
    cF
    vx
    cV
    c.0
    cmpt
    vv
    cV
    c.0
    cmpt
    lincvalsc0.f
    vx
    vv
    cV
    c.0
    c.0
    vx
    vv
    weq
    c.0
    eqidd
    cbvmptv
    eqtri
    @0
    @2
    simpr
    c.0
    cvv
    wcel
    #
    @3
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
    #
    a1i
    #
    @14
    @3
    vv
    cv
    cV
    wcel
    wa
    @15
    a1i
    mptsuppd
    @3
    @13
    c0
    cfn
    @3
    @12
    wn
    #
    vv
    cV
    wral
    @13
    c0
    wceq
    @3
    @17
    vv
    cV
    @17
    @3
    c.0
    neirr
    a1i
    ralrimivw
    @12
    vv
    cV
    rabeq0
    sylibr
    c0
    cfn
    wcel
    @3
    0fin
    a1i
    eqeltrd
    eqeltrd
    @3
    cF
    wfun
    #
    @5
    @14
    @6
    @11
    wb
    @18
    @3
    vx
    cV
    c.0
    cF
    lincvalsc0.f
    funmpt2
    a1i
    @9
    @16
    cF
    @4
    cvv
    c.0
    funisfsupp
    syl3anc
    mpbird
    vx
    cB
    cS
    cF
    cM
    cV
    c.0
    cZ
    lincvalsc0.b
    lincvalsc0.s
    lincvalsc0.0
    lincvalsc0.z
    lincvalsc0.f
    lincvalsc0
    3jca
end
