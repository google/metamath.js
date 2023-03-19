include "cc.mm"
include "wss.mm"
include "cpm.mm"
include "co.mm"
include "wcel.mm"
include "wa.mm"
include "cc0.mm"
include "cdvn.mm"
include "cfv.mm"
include "cvv.mm"
include "cv.mm"
include "cdv.mm"
include "cmpt.mm"
include "c1st.mm"
include "ccom.mm"
include "cn0.mm"
include "csn.mm"
include "cxp.mm"
include "cseq.mm"
include "eqid.mm"
include "dvnfval.mm"
include "fveq1d.mm"
include "0z.mm"
include "wceq.mm"
include "simpr.mm"
include "0nn0.mm"
include "fvconst2g.mm"
include "sylancl.mm"
include "seq1i.mm"
include "eqtrd.mm"

theorem dvn0
  let cS: class S
  let cF: class F
  let vf: setvar f
  let vk: setvar k
  let vn: setvar n
  let vx: setvar x
  let vm: setvar m
  let cM: class M
  let cN: class N
  let vs: setvar s


  assert |- ( ( S C_ CC /\ F e. ( CC ^pm S ) ) -> ( ( S Dn F ) ` 0 ) = F )

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
    cc0
    cS
    cF
    cdvn
    co
    #
    cfv
    cc0
    vx
    cvv
    cS
    vx
    cv
    cdv
    co
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
    cF
    @3
    cc0
    @4
    @8
    vx
    cS
    cF
    @5
    @5
    eqid
    dvnfval
    fveq1d
    @3
    cF
    @6
    @7
    cc0
    0z
    @3
    @2
    cc0
    cn0
    wcel
    cc0
    @7
    cfv
    cF
    wceq
    @0
    @2
    simpr
    0nn0
    cn0
    cF
    cc0
    @1
    fvconst2g
    sylancl
    seq1i
    eqtrd
end
