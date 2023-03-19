include "cc.mm"
include "wss.mm"
include "cpm.mm"
include "co.mm"
include "wcel.mm"
include "cn0.mm"
include "w3a.mm"
include "c1.mm"
include "caddc.mm"
include "cvv.mm"
include "cv.mm"
include "cdv.mm"
include "cmpt.mm"
include "c1st.mm"
include "ccom.mm"
include "csn.mm"
include "cxp.mm"
include "cc0.mm"
include "cseq.mm"
include "cfv.mm"
include "cdvn.mm"
include "cuz.mm"
include "wceq.mm"
include "simp3.mm"
include "nn0uz.mm"
include "syl6eleq.mm"
include "seqp1.mm"
include "syl.mm"
include "fvex.mm"
include "algrflem.mm"
include "syl6eq.mm"
include "eqid.mm"
include "dvnfval.mm"
include "3adant3.mm"
include "fveq1d.mm"
include "oveq2.mm"
include "ovex.mm"
include "fvmpt.mm"
include "ax-mp.mm"
include "fveq2d.mm"
include "syl5eqr.mm"
include "3eqtr4d.mm"

theorem dvnp1
  let cS: class S
  let cF: class F
  let cN: class N
  let vf: setvar f
  let vk: setvar k
  let vn: setvar n
  let vx: setvar x
  let vm: setvar m
  let cM: class M
  let vs: setvar s


  assert |- ( ( S C_ CC /\ F e. ( CC ^pm S ) /\ N e. NN0 ) -> ( ( S Dn F ) ` ( N + 1 ) ) = ( S _D ( ( S Dn F ) ` N ) ) )

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
    wcel
    #
    cN
    cn0
    wcel
    #
    w3a
    #
    cN
    c1
    caddc
    co
    #
    vx
    cvv
    cS
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
    cF
    csn
    cxp
    #
    cc0
    cseq
    #
    cfv
    #
    cN
    @10
    cfv
    #
    @7
    cfv
    #
    @4
    cS
    cF
    cdvn
    co
    #
    cfv
    cS
    cN
    @14
    cfv
    #
    cdv
    co
    #
    @3
    @11
    @12
    @4
    @9
    cfv
    #
    @8
    co
    #
    @13
    @3
    cN
    cc0
    cuz
    cfv
    #
    wcel
    @11
    @18
    wceq
    @3
    cN
    cn0
    @19
    @0
    @1
    @2
    simp3
    nn0uz
    syl6eleq
    @8
    @9
    cc0
    cN
    seqp1
    syl
    @12
    @17
    @7
    cN
    @10
    fvex
    @4
    @9
    fvex
    algrflem
    syl6eq
    @3
    @4
    @14
    @10
    @0
    @1
    @14
    @10
    wceq
    @2
    vx
    cS
    cF
    @7
    @7
    eqid
    #
    dvnfval
    3adant3
    #
    fveq1d
    @3
    @16
    @15
    @7
    cfv
    #
    @13
    @15
    cvv
    wcel
    @22
    @16
    wceq
    cN
    @14
    fvex
    vx
    @15
    @6
    @16
    cvv
    @7
    @5
    @15
    cS
    cdv
    oveq2
    @20
    cS
    @15
    cdv
    ovex
    fvmpt
    ax-mp
    @3
    @15
    @12
    @7
    @3
    cN
    @14
    @10
    @21
    fveq1d
    fveq2d
    syl5eqr
    3eqtr4d
end
