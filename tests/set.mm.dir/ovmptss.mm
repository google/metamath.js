include "cv.mm"
include "c1st.mm"
include "cfv.mm"
include "c2nd.mm"
include "csb.mm"
include "wss.mm"
include "csn.mm"
include "cxp.mm"
include "ciun.mm"
include "wral.mm"
include "cop.mm"
include "co.mm"
include "cmpt2.mm"
include "cmpt.mm"
include "mpt2mptsx.mm"
include "eqtri.mm"
include "fvmptss.mm"
include "wceq.mm"
include "vex.mm"
include "op1std.mm"
include "csbeq1d.mm"
include "op2ndd.mm"
include "csbeq2dv.mm"
include "eqtrd.mm"
include "sseq1d.mm"
include "raliunxp.mm"
include "nfcv.mm"
include "nfcsb1v.mm"
include "nfxp.mm"
include "weq.mm"
include "sneq.mm"
include "csbeq1a.mm"
include "xpeq12d.mm"
include "cbviun.mm"
include "raleqi.mm"
include "nfv.mm"
include "nfss.mm"
include "nfral.mm"
include "cbvral.mm"
include "raleqbidv.mm"
include "syl5bb.mm"
include "3bitr4ri.mm"
include "df-ov.mm"
include "sseq1i.mm"
include "3imtr4i.mm"

theorem ovmptss
  let vx: setvar x
  let vy: setvar y
  let cA: class A
  let cB: class B
  let cC: class C
  let cE: class E
  let cF: class F
  let cG: class G
  let cX: class X
  let vu: setvar u
  let vv: setvar v
  let vz: setvar z
  assume ovmptss.1: |- F = ( x e. A , y e. B |-> C )

  disjoint x y
  disjoint A x
  disjoint A y
  disjoint B y
  disjoint X x
  disjoint X y
  disjoint u v
  disjoint u x
  disjoint u y
  disjoint u z
  disjoint A u
  disjoint v x
  disjoint v y
  disjoint v z
  disjoint A v
  disjoint x z
  disjoint y z
  disjoint A z
  disjoint B u
  disjoint B v
  disjoint B z
  disjoint C u
  disjoint C v
  disjoint C z
  disjoint X u
  disjoint X v
  disjoint X z
  assert |- ( A. x e. A A. y e. B C C_ X -> ( E F G ) C_ X )

  proof
    vx
    vz
    cv
    #
    c1st
    cfv
    #
    vy
    @0
    c2nd
    cfv
    #
    cC
    csb
    #
    csb
    #
    cX
    wss
    #
    vz
    vx
    cA
    vx
    cv
    #
    csn
    #
    cB
    cxp
    #
    ciun
    #
    wral
    #
    cE
    cG
    cop
    #
    cF
    cfv
    #
    cX
    wss
    cC
    cX
    wss
    #
    vy
    cB
    wral
    #
    vx
    cA
    wral
    #
    cE
    cG
    cF
    co
    #
    cX
    wss
    vz
    @9
    @4
    cX
    @11
    cF
    cF
    vx
    vy
    cA
    cB
    cC
    cmpt2
    vz
    @9
    @4
    cmpt
    ovmptss.1
    vx
    vy
    vz
    cA
    cB
    cC
    mpt2mptsx
    eqtri
    fvmptss
    @5
    vz
    vu
    cA
    vu
    cv
    #
    csn
    #
    vx
    @17
    cB
    csb
    #
    cxp
    #
    ciun
    #
    wral
    vx
    @17
    vy
    vv
    cv
    #
    cC
    csb
    #
    csb
    #
    cX
    wss
    #
    vv
    @19
    wral
    #
    vu
    cA
    wral
    @10
    @15
    @5
    @25
    vz
    vu
    vv
    cA
    @19
    @0
    @17
    @22
    cop
    wceq
    #
    @4
    @24
    cX
    @27
    @4
    vx
    @17
    @3
    csb
    @24
    @27
    vx
    @1
    @17
    @3
    @17
    @22
    @0
    vu
    vex
    #
    vv
    vex
    #
    op1std
    csbeq1d
    @27
    vx
    @17
    @3
    @23
    @27
    vy
    @2
    @22
    cC
    @17
    @22
    @0
    @28
    @29
    op2ndd
    csbeq1d
    csbeq2dv
    eqtrd
    sseq1d
    raliunxp
    @5
    vz
    @9
    @21
    vx
    vu
    cA
    @8
    @20
    vu
    @8
    nfcv
    vx
    @18
    @19
    vx
    @18
    nfcv
    vx
    @17
    cB
    nfcsb1v
    #
    nfxp
    vx
    vu
    weq
    #
    @7
    @18
    cB
    @19
    @6
    @17
    sneq
    vx
    @17
    cB
    csbeq1a
    #
    xpeq12d
    cbviun
    raleqi
    @14
    @26
    vx
    vu
    cA
    @14
    vu
    nfv
    @25
    vx
    vv
    @19
    @30
    vx
    @24
    cX
    vx
    @17
    @23
    nfcsb1v
    vx
    cX
    nfcv
    nfss
    nfral
    @14
    @23
    cX
    wss
    #
    vv
    cB
    wral
    @31
    @26
    @13
    @33
    vy
    vv
    cB
    @13
    vv
    nfv
    vy
    @23
    cX
    vy
    @22
    cC
    nfcsb1v
    vy
    cX
    nfcv
    nfss
    vy
    vv
    weq
    cC
    @23
    cX
    vy
    @22
    cC
    csbeq1a
    sseq1d
    cbvral
    @31
    @33
    @25
    vv
    cB
    @19
    @32
    @31
    @23
    @24
    cX
    vx
    @17
    @23
    csbeq1a
    sseq1d
    raleqbidv
    syl5bb
    cbvral
    3bitr4ri
    @16
    @12
    cX
    cE
    cG
    cF
    df-ov
    sseq1i
    3imtr4i
end
