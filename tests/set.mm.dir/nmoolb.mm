include "cnv.mm"
include "wcel.mm"
include "wf.mm"
include "w3a.mm"
include "cfv.mm"
include "c1.mm"
include "cle.mm"
include "wbr.mm"
include "wa.mm"
include "cv.mm"
include "wceq.mm"
include "wrex.mm"
include "cab.mm"
include "cxr.mm"
include "clt.mm"
include "csup.mm"
include "wss.mm"
include "cr.mm"
include "nmosetre.mm"
include "ressxr.mm"
include "syl6ss.mm"
include "3adant1.mm"
include "fveq2.mm"
include "breq1d.mm"
include "fveq2d.mm"
include "eqeq2d.mm"
include "anbi12d.mm"
include "eqid.mm"
include "biantru.mm"
include "syl6bbr.mm"
include "rspcev.mm"
include "fvex.mm"
include "eqeq1.mm"
include "anbi2d.mm"
include "rexbidv.mm"
include "elab.mm"
include "sylibr.mm"
include "supxrub.mm"
include "syl2an.mm"
include "nmooval.mm"
include "adantr.mm"
include "breqtrrd.mm"

theorem nmoolb
  let cA: class A
  let cT: class T
  let cU: class U
  let cL: class L
  let cM: class M
  let cN: class N
  let cW: class W
  let cX: class X
  let cY: class Y
  let vx: setvar x
  let vy: setvar y
  assume nmoolb.1: |- X = ( BaseSet ` U )
  assume nmoolb.2: |- Y = ( BaseSet ` W )
  assume nmoolb.l: |- L = ( normCV ` U )
  assume nmoolb.m: |- M = ( normCV ` W )
  assume nmoolb.3: |- N = ( U normOpOLD W )


  assert |- ( ( ( U e. NrmCVec /\ W e. NrmCVec /\ T : X --> Y ) /\ ( A e. X /\ ( L ` A ) <_ 1 ) ) -> ( M ` ( T ` A ) ) <_ ( N ` T ) )

  proof
    cU
    cnv
    wcel
    #
    cW
    cnv
    wcel
    #
    cX
    cY
    cT
    wf
    #
    w3a
    #
    cA
    cX
    wcel
    cA
    cL
    cfv
    #
    c1
    cle
    wbr
    #
    wa
    #
    wa
    cA
    cT
    cfv
    #
    cM
    cfv
    #
    vy
    cv
    #
    cL
    cfv
    #
    c1
    cle
    wbr
    #
    vx
    cv
    #
    @9
    cT
    cfv
    #
    cM
    cfv
    #
    wceq
    #
    wa
    #
    vy
    cX
    wrex
    #
    vx
    cab
    #
    cxr
    clt
    csup
    #
    cT
    cN
    cfv
    #
    cle
    @3
    @18
    cxr
    wss
    #
    @8
    @18
    wcel
    #
    @8
    @19
    cle
    wbr
    @6
    @1
    @2
    @21
    @0
    @1
    @2
    wa
    @18
    cr
    cxr
    vx
    vy
    cT
    cL
    cM
    cW
    cX
    cY
    nmoolb.2
    nmoolb.m
    nmosetre
    ressxr
    syl6ss
    3adant1
    @6
    @11
    @8
    @14
    wceq
    #
    wa
    #
    vy
    cX
    wrex
    #
    @22
    @24
    @5
    vy
    cA
    cX
    @9
    cA
    wceq
    #
    @24
    @5
    @8
    @8
    wceq
    #
    wa
    @5
    @26
    @11
    @5
    @23
    @27
    @26
    @10
    @4
    c1
    cle
    @9
    cA
    cL
    fveq2
    breq1d
    @26
    @14
    @8
    @8
    @26
    @13
    @7
    cM
    @9
    cA
    cT
    fveq2
    fveq2d
    eqeq2d
    anbi12d
    @27
    @5
    @8
    eqid
    biantru
    syl6bbr
    rspcev
    @17
    @25
    vx
    @8
    @7
    cM
    fvex
    @12
    @8
    wceq
    #
    @16
    @24
    vy
    cX
    @28
    @15
    @23
    @11
    @12
    @8
    @14
    eqeq1
    anbi2d
    rexbidv
    elab
    sylibr
    @18
    @8
    supxrub
    syl2an
    @3
    @20
    @19
    wceq
    @6
    vx
    vy
    cT
    cU
    cL
    cM
    cN
    cW
    cX
    cY
    nmoolb.1
    nmoolb.2
    nmoolb.l
    nmoolb.m
    nmoolb.3
    nmooval
    adantr
    breqtrrd
end
