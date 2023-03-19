include "ctopon.mm"
include "cfv.mm"
include "wcel.mm"
include "wa.mm"
include "cv.mm"
include "cop.mm"
include "cmpt2.mm"
include "ctx.mm"
include "co.mm"
include "ccn.mm"
include "ccnv.mm"
include "chmeo.mm"
include "simpl.mm"
include "simpr.mm"
include "cnmpt2nd.mm"
include "cnmpt1st.mm"
include "cnmpt2t.mm"
include "cxp.mm"
include "wf1o.mm"
include "wceq.mm"
include "wf.mm"
include "wral.mm"
include "opelxpi.mm"
include "ancoms.mm"
include "adantl.mm"
include "ralrimivva.mm"
include "eqid.mm"
include "fmpt2.mm"
include "sylib.mm"
include "ccom.mm"
include "cid.mm"
include "cres.mm"
include "txswaphmeolem.mm"
include "fcof1o.mm"
include "mpanr12.mm"
include "syl2anc.mm"
include "simprd.mm"
include "eqeltrd.mm"
include "ishmeo.mm"
include "sylanbrc.mm"

theorem txswaphmeo
  let vx: setvar x
  let vy: setvar y
  let cJ: class J
  let cK: class K
  let cX: class X
  let cY: class Y
  let vz: setvar z

  disjoint x y
  disjoint J x
  disjoint J y
  disjoint K x
  disjoint K y
  disjoint X x
  disjoint X y
  disjoint Y x
  disjoint Y y
  disjoint x z
  disjoint y z
  disjoint X z
  disjoint Y z
  assert |- ( ( J e. ( TopOn ` X ) /\ K e. ( TopOn ` Y ) ) -> ( x e. X , y e. Y |-> <. y , x >. ) e. ( ( J tX K ) Homeo ( K tX J ) ) )

  proof
    cJ
    cX
    ctopon
    cfv
    wcel
    #
    cK
    cY
    ctopon
    cfv
    wcel
    #
    wa
    #
    vx
    vy
    cX
    cY
    vy
    cv
    #
    vx
    cv
    #
    cop
    #
    cmpt2
    #
    cJ
    cK
    ctx
    co
    #
    cK
    cJ
    ctx
    co
    #
    ccn
    co
    wcel
    @6
    ccnv
    #
    @8
    @7
    ccn
    co
    #
    wcel
    @6
    @7
    @8
    chmeo
    co
    wcel
    @2
    vx
    vy
    @3
    @4
    cJ
    cK
    cK
    cJ
    cX
    cY
    @0
    @1
    simpl
    #
    @0
    @1
    simpr
    #
    @2
    vx
    vy
    cJ
    cK
    cX
    cY
    @11
    @12
    cnmpt2nd
    @2
    vx
    vy
    cJ
    cK
    cX
    cY
    @11
    @12
    cnmpt1st
    cnmpt2t
    @2
    @9
    vy
    vx
    cY
    cX
    @4
    @3
    cop
    #
    cmpt2
    #
    @10
    @2
    cX
    cY
    cxp
    #
    cY
    cX
    cxp
    #
    @6
    wf1o
    #
    @9
    @14
    wceq
    #
    @2
    @15
    @16
    @6
    wf
    #
    @16
    @15
    @14
    wf
    #
    @17
    @18
    wa
    #
    @2
    @5
    @16
    wcel
    #
    vy
    cY
    wral
    vx
    cX
    wral
    @19
    @2
    @22
    vx
    vy
    cX
    cY
    @4
    cX
    wcel
    #
    @3
    cY
    wcel
    #
    wa
    @22
    @2
    @24
    @23
    @22
    @3
    @4
    cY
    cX
    opelxpi
    ancoms
    adantl
    ralrimivva
    vx
    vy
    cX
    cY
    @5
    @16
    @6
    @6
    eqid
    fmpt2
    sylib
    @2
    @13
    @15
    wcel
    #
    vx
    cX
    wral
    vy
    cY
    wral
    @20
    @2
    @25
    vy
    vx
    cY
    cX
    @24
    @23
    wa
    @25
    @2
    @23
    @24
    @25
    @4
    @3
    cX
    cY
    opelxpi
    ancoms
    adantl
    ralrimivva
    vy
    vx
    cY
    cX
    @13
    @15
    @14
    @14
    eqid
    fmpt2
    sylib
    @19
    @20
    wa
    @6
    @14
    ccom
    cid
    @16
    cres
    wceq
    @14
    @6
    ccom
    cid
    @15
    cres
    wceq
    @21
    vy
    vx
    cY
    cX
    txswaphmeolem
    vx
    vy
    cX
    cY
    txswaphmeolem
    @15
    @16
    @6
    @14
    fcof1o
    mpanr12
    syl2anc
    simprd
    @2
    vy
    vx
    @4
    @3
    cK
    cJ
    cJ
    cK
    cY
    cX
    @12
    @11
    @2
    vy
    vx
    cK
    cJ
    cY
    cX
    @12
    @11
    cnmpt2nd
    @2
    vy
    vx
    cK
    cJ
    cY
    cX
    @12
    @11
    cnmpt1st
    cnmpt2t
    eqeltrd
    @6
    @7
    @8
    ishmeo
    sylanbrc
end
