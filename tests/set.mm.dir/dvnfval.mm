include "cc.mm"
include "wss.mm"
include "cpm.mm"
include "co.mm"
include "wcel.mm"
include "wa.mm"
include "cpw.mm"
include "cv.mm"
include "cvv.mm"
include "cdv.mm"
include "cmpt.mm"
include "c1st.mm"
include "ccom.mm"
include "cn0.mm"
include "csn.mm"
include "cxp.mm"
include "cc0.mm"
include "cseq.mm"
include "cdvn.mm"
include "cmpt2.mm"
include "wceq.mm"
include "df-dvn.mm"
include "a1i.mm"
include "simprl.mm"
include "oveq1d.mm"
include "mpteq2dv.mm"
include "syl6eqr.mm"
include "coeq1d.mm"
include "seqeq2d.mm"
include "simprr.mm"
include "sneqd.mm"
include "xpeq2d.mm"
include "seqeq3d.mm"
include "eqtrd.mm"
include "simpr.mm"
include "oveq2d.mm"
include "simpl.mm"
include "cnex.mm"
include "elpw2.mm"
include "sylibr.mm"
include "seqex.mm"
include "ovmpt2dx.mm"

theorem dvnfval
  let vx: setvar x
  let cS: class S
  let cF: class F
  let cG: class G
  let vf: setvar f
  let vs: setvar s
  assume dvnfval.1: |- G = ( x e. _V |-> ( S _D x ) )

  disjoint F x
  disjoint S x
  disjoint f s
  disjoint f x
  disjoint F f
  disjoint s x
  disjoint F s
  disjoint G f
  disjoint G s
  disjoint S f
  disjoint S s
  assert |- ( ( S C_ CC /\ F e. ( CC ^pm S ) ) -> ( S Dn F ) = seq 0 ( ( G o. 1st ) , ( NN0 X. { F } ) ) )

  proof
    cS
    cc
    wss
    #
    cF
    cc
    cS
    cpm
    co
    #
    wcel
    #
    wa
    #
    vs
    vf
    cS
    cF
    cc
    cpw
    #
    cc
    vs
    cv
    #
    cpm
    co
    #
    vx
    cvv
    @5
    vx
    cv
    #
    cdv
    co
    #
    cmpt
    #
    c1st
    ccom
    #
    cn0
    vf
    cv
    #
    csn
    #
    cxp
    #
    cc0
    cseq
    #
    cG
    c1st
    ccom
    #
    cn0
    cF
    csn
    #
    cxp
    #
    cc0
    cseq
    #
    cdvn
    @1
    cvv
    cdvn
    vs
    vf
    @4
    @6
    @14
    cmpt2
    wceq
    @3
    vx
    vf
    vs
    df-dvn
    a1i
    @3
    @5
    cS
    wceq
    #
    @11
    cF
    wceq
    #
    wa
    wa
    #
    @14
    @15
    @13
    cc0
    cseq
    @18
    @21
    @10
    @15
    @13
    cc0
    @21
    @9
    cG
    c1st
    @21
    @9
    vx
    cvv
    cS
    @7
    cdv
    co
    #
    cmpt
    cG
    @21
    vx
    cvv
    @8
    @22
    @21
    @5
    cS
    @7
    cdv
    @3
    @19
    @20
    simprl
    oveq1d
    mpteq2dv
    dvnfval.1
    syl6eqr
    coeq1d
    seqeq2d
    @21
    @13
    @17
    @15
    cc0
    @21
    @12
    @16
    cn0
    @21
    @11
    cF
    @3
    @19
    @20
    simprr
    sneqd
    xpeq2d
    seqeq3d
    eqtrd
    @3
    @19
    wa
    @5
    cS
    cc
    cpm
    @3
    @19
    simpr
    oveq2d
    @3
    @0
    cS
    @4
    wcel
    @0
    @2
    simpl
    cS
    cc
    cnex
    elpw2
    sylibr
    @0
    @2
    simpr
    @18
    cvv
    wcel
    @3
    @15
    @17
    cc0
    seqex
    a1i
    ovmpt2dx
end
