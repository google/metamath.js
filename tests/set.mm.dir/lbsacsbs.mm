include "clvec.mm"
include "wcel.mm"
include "wss.mm"
include "clspn.mm"
include "cfv.mm"
include "wceq.mm"
include "cv.mm"
include "csn.mm"
include "cdif.mm"
include "wn.mm"
include "wral.mm"
include "w3a.mm"
include "wa.mm"
include "eqid.mm"
include "islbs2.mm"
include "clmod.mm"
include "lveclmod.mm"
include "mrclsp.mm"
include "syl.mm"
include "fveq1d.mm"
include "eqeq1d.mm"
include "eleq2d.mm"
include "notbid.mm"
include "ralbidv.mm"
include "3anbi23d.mm"
include "cmre.mm"
include "wb.mm"
include "lssmre.mm"
include "ismri.mm"
include "3syl.mm"
include "anbi1d.mm"
include "3anan32.mm"
include "syl6rbbr.mm"
include "3bitrd.mm"

theorem lbsacsbs
  let cA: class A
  let cS: class S
  let cI: class I
  let cJ: class J
  let cN: class N
  let cW: class W
  let cX: class X
  let vx: setvar x
  assume lbsacsbs.1: |- A = ( LSubSp ` W )
  assume lbsacsbs.2: |- N = ( mrCls ` A )
  assume lbsacsbs.3: |- X = ( Base ` W )
  assume lbsacsbs.4: |- I = ( mrInd ` A )
  assume lbsacsbs.5: |- J = ( LBasis ` W )


  assert |- ( W e. LVec -> ( S e. J <-> ( S e. I /\ ( N ` S ) = X ) ) )

  proof
    cW
    clvec
    wcel
    #
    cS
    cJ
    wcel
    cS
    cX
    wss
    #
    cS
    cW
    clspn
    cfv
    #
    cfv
    #
    cX
    wceq
    #
    vx
    cv
    #
    cS
    @5
    csn
    cdif
    #
    @2
    cfv
    #
    wcel
    #
    wn
    #
    vx
    cS
    wral
    #
    w3a
    @1
    cS
    cN
    cfv
    #
    cX
    wceq
    #
    @5
    @6
    cN
    cfv
    #
    wcel
    #
    wn
    #
    vx
    cS
    wral
    #
    w3a
    #
    cS
    cI
    wcel
    #
    @12
    wa
    #
    vx
    cS
    cJ
    @2
    cX
    cW
    lbsacsbs.3
    lbsacsbs.5
    @2
    eqid
    #
    islbs2
    @0
    @4
    @12
    @10
    @16
    @1
    @0
    @3
    @11
    cX
    @0
    cS
    @2
    cN
    @0
    cW
    clmod
    wcel
    #
    @2
    cN
    wceq
    cW
    lveclmod
    #
    cA
    cN
    @2
    cW
    lbsacsbs.1
    @20
    lbsacsbs.2
    mrclsp
    syl
    #
    fveq1d
    eqeq1d
    @0
    @9
    @15
    vx
    cS
    @0
    @8
    @14
    @0
    @7
    @13
    @5
    @0
    @6
    @2
    cN
    @23
    fveq1d
    eleq2d
    notbid
    ralbidv
    3anbi23d
    @0
    @19
    @1
    @16
    wa
    #
    @12
    wa
    @17
    @0
    @18
    @24
    @12
    @0
    @21
    cA
    cX
    cmre
    cfv
    wcel
    @18
    @24
    wb
    @22
    cX
    cA
    cW
    lbsacsbs.3
    lbsacsbs.1
    lssmre
    vx
    cA
    cS
    cI
    cN
    cX
    lbsacsbs.2
    lbsacsbs.4
    ismri
    3syl
    anbi1d
    @1
    @12
    @16
    3anan32
    syl6rbbr
    3bitrd
end
