include "ctmd.mm"
include "wcel.mm"
include "wa.mm"
include "co.mm"
include "w3a.mm"
include "cv.mm"
include "cxp.mm"
include "cplusf.mm"
include "cfv.mm"
include "ccnv.mm"
include "cima.mm"
include "wss.mm"
include "wrex.mm"
include "wral.mm"
include "ctopon.mm"
include "tmdtopon.mm"
include "ad2antrr.mm"
include "ctx.mm"
include "ccn.mm"
include "cop.mm"
include "cuni.mm"
include "ccnp.mm"
include "eqid.mm"
include "tmdcn.mm"
include "simpr1.mm"
include "simpr2.mm"
include "opelxpi.mm"
include "syl2anc.mm"
include "wceq.mm"
include "txtopon.mm"
include "toponuni.mm"
include "syl.mm"
include "eleqtrd.mm"
include "cncnpi.mm"
include "simplr.mm"
include "plusfval.mm"
include "simpr3.mm"
include "eqeltrd.mm"
include "txcnpi.mm"
include "dfss3.mm"
include "eleq1.mm"
include "wfn.mm"
include "wb.mm"
include "plusffn.mm"
include "elpreima.mm"
include "ax-mp.mm"
include "syl6bb.mm"
include "ralxp.mm"
include "bitri.mm"
include "opelxp.mm"
include "df-ov.mm"
include "syl5eqr.mm"
include "sylbi.mm"
include "eleq1d.mm"
include "biimpa.mm"
include "2ralimi.mm"
include "3anim3i.mm"
include "reximi.mm"

theorem tmdcn2
  let vx: setvar x
  let vy: setvar y
  let vv: setvar v
  let vu: setvar u
  let cB: class B
  let c.pl: class .+
  let cU: class U
  let cG: class G
  let cJ: class J
  let cX: class X
  let cY: class Y
  let vz: setvar z
  assume tmdcn2.1: |- B = ( Base ` G )
  assume tmdcn2.2: |- J = ( TopOpen ` G )
  assume tmdcn2.3: |- .+ = ( +g ` G )

  disjoint u v
  disjoint u x
  disjoint u y
  disjoint G u
  disjoint v x
  disjoint v y
  disjoint G v
  disjoint x y
  disjoint G x
  disjoint G y
  disjoint J u
  disjoint J v
  disjoint U u
  disjoint U v
  disjoint U x
  disjoint U y
  disjoint X u
  disjoint X v
  disjoint Y u
  disjoint Y v
  disjoint u z
  disjoint v z
  disjoint x z
  disjoint y z
  disjoint G z
  disjoint U z
  disjoint B z
  assert |- ( ( ( G e. TopMnd /\ U e. J ) /\ ( X e. B /\ Y e. B /\ ( X .+ Y ) e. U ) ) -> E. u e. J E. v e. J ( X e. u /\ Y e. v /\ A. x e. u A. y e. v ( x .+ y ) e. U ) )

  proof
    cG
    ctmd
    wcel
    #
    cU
    cJ
    wcel
    #
    wa
    #
    cX
    cB
    wcel
    #
    cY
    cB
    wcel
    #
    cX
    cY
    c.pl
    co
    #
    cU
    wcel
    #
    w3a
    #
    wa
    #
    cX
    vu
    cv
    #
    wcel
    #
    cY
    vv
    cv
    #
    wcel
    #
    @9
    @11
    cxp
    #
    cG
    cplusf
    cfv
    #
    ccnv
    cU
    cima
    #
    wss
    #
    w3a
    #
    vv
    cJ
    wrex
    #
    vu
    cJ
    wrex
    @10
    @12
    vx
    cv
    #
    vy
    cv
    #
    c.pl
    co
    #
    cU
    wcel
    #
    vy
    @11
    wral
    vx
    @9
    wral
    #
    w3a
    #
    vv
    cJ
    wrex
    #
    vu
    cJ
    wrex
    @8
    vv
    vu
    cX
    cY
    cU
    @14
    cJ
    cJ
    cJ
    cB
    cB
    @0
    cJ
    cB
    ctopon
    cfv
    wcel
    #
    @1
    @7
    cG
    cJ
    cB
    tmdcn2.2
    tmdcn2.1
    tmdtopon
    ad2antrr
    #
    @27
    @8
    @14
    cJ
    cJ
    ctx
    co
    #
    cJ
    ccn
    co
    wcel
    #
    cX
    cY
    cop
    #
    @28
    cuni
    #
    wcel
    @14
    @30
    @28
    cJ
    ccnp
    co
    cfv
    wcel
    @0
    @29
    @1
    @7
    @14
    cG
    cJ
    tmdcn2.2
    @14
    eqid
    #
    tmdcn
    ad2antrr
    @8
    @30
    cB
    cB
    cxp
    #
    @31
    @8
    @3
    @4
    @30
    @33
    wcel
    @2
    @3
    @4
    @6
    simpr1
    #
    @2
    @3
    @4
    @6
    simpr2
    #
    cX
    cY
    cB
    cB
    opelxpi
    syl2anc
    @8
    @28
    @33
    ctopon
    cfv
    wcel
    #
    @33
    @31
    wceq
    @8
    @26
    @26
    @36
    @27
    @27
    cJ
    cJ
    cB
    cB
    txtopon
    syl2anc
    @33
    @28
    toponuni
    syl
    eleqtrd
    @30
    @14
    @28
    cJ
    @31
    @31
    eqid
    cncnpi
    syl2anc
    @0
    @1
    @7
    simplr
    @34
    @35
    @8
    cX
    cY
    @14
    co
    #
    @5
    cU
    @8
    @3
    @4
    @37
    @5
    wceq
    @34
    @35
    cB
    c.pl
    @14
    cG
    cX
    cY
    tmdcn2.1
    tmdcn2.3
    @32
    plusfval
    syl2anc
    @2
    @3
    @4
    @6
    simpr3
    eqeltrd
    txcnpi
    @18
    @25
    vu
    cJ
    @17
    @24
    vv
    cJ
    @16
    @23
    @10
    @12
    @16
    @19
    @20
    cop
    #
    @33
    wcel
    #
    @38
    @14
    cfv
    #
    cU
    wcel
    #
    wa
    #
    vy
    @11
    wral
    vx
    @9
    wral
    #
    @23
    @16
    vz
    cv
    #
    @15
    wcel
    #
    vz
    @13
    wral
    @43
    vz
    @13
    @15
    dfss3
    @45
    @42
    vz
    vx
    vy
    @9
    @11
    @44
    @38
    wceq
    @45
    @38
    @15
    wcel
    #
    @42
    @44
    @38
    @15
    eleq1
    @14
    @33
    wfn
    @46
    @42
    wb
    cB
    @14
    cG
    tmdcn2.1
    @32
    plusffn
    @33
    @38
    cU
    @14
    elpreima
    ax-mp
    syl6bb
    ralxp
    bitri
    @42
    @22
    vx
    vy
    @9
    @11
    @39
    @41
    @22
    @39
    @40
    @21
    cU
    @39
    @19
    cB
    wcel
    @20
    cB
    wcel
    wa
    #
    @40
    @21
    wceq
    @19
    @20
    cB
    cB
    opelxp
    @47
    @40
    @19
    @20
    @14
    co
    @21
    @19
    @20
    @14
    df-ov
    cB
    c.pl
    @14
    cG
    @19
    @20
    tmdcn2.1
    tmdcn2.3
    @32
    plusfval
    syl5eqr
    sylbi
    eleq1d
    biimpa
    2ralimi
    sylbi
    3anim3i
    reximi
    reximi
    syl
end
