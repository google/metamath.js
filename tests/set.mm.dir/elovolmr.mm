include "cn.mm"
include "cle.mm"
include "cr.mm"
include "cxp.mm"
include "cin.mm"
include "wf.mm"
include "cioo.mm"
include "ccom.mm"
include "crn.mm"
include "cuni.mm"
include "wss.mm"
include "wa.mm"
include "cv.mm"
include "cxr.mm"
include "clt.mm"
include "csup.mm"
include "caddc.mm"
include "cabs.mm"
include "cmin.mm"
include "c1.mm"
include "cseq.mm"
include "wceq.mm"
include "cmap.mm"
include "co.mm"
include "wrex.mm"
include "wcel.mm"
include "reex.mm"
include "xpex.mm"
include "inex2.mm"
include "nnex.mm"
include "elmap.mm"
include "id.mm"
include "eqcomd.mm"
include "coeq2d.mm"
include "seqeq3d.mm"
include "syl5eq.mm"
include "rneqd.mm"
include "supeq1d.mm"
include "biantrud.mm"
include "coeq2.mm"
include "unieqd.mm"
include "sseq2d.mm"
include "bitr3d.mm"
include "rspcev.mm"
include "sylanbr.mm"
include "elovolm.mm"
include "sylibr.mm"

theorem elovolmr
  let vy: setvar y
  let cA: class A
  let cS: class S
  let vf: setvar f
  let cF: class F
  let cM: class M
  let vx: setvar x
  let cB: class B
  assume ovolval.1: |- M = { y e. RR* | E. f e. ( ( <_ i^i ( RR X. RR ) ) ^m NN ) ( A C_ U. ran ( (,) o. f ) /\ y = sup ( ran seq 1 ( + , ( ( abs o. - ) o. f ) ) , RR* , < ) ) }
  assume ovolval.2: |- S = seq 1 ( + , ( ( abs o. - ) o. F ) )

  disjoint f y
  disjoint A f
  disjoint A y
  disjoint F f
  disjoint S f
  disjoint S y
  disjoint f x
  disjoint x y
  disjoint A x
  disjoint B f
  disjoint B y
  disjoint M x
  assert |- ( ( F : NN --> ( <_ i^i ( RR X. RR ) ) /\ A C_ U. ran ( (,) o. F ) ) -> sup ( ran S , RR* , < ) e. M )

  proof
    cn
    cle
    cr
    cr
    cxp
    #
    cin
    #
    cF
    wf
    #
    cA
    cioo
    cF
    ccom
    #
    crn
    #
    cuni
    #
    wss
    #
    wa
    cA
    cioo
    vf
    cv
    #
    ccom
    #
    crn
    #
    cuni
    #
    wss
    #
    cS
    crn
    #
    cxr
    clt
    csup
    #
    caddc
    cabs
    cmin
    ccom
    #
    @7
    ccom
    #
    c1
    cseq
    #
    crn
    #
    cxr
    clt
    csup
    wceq
    #
    wa
    #
    vf
    @1
    cn
    cmap
    co
    #
    wrex
    #
    @13
    cM
    wcel
    @2
    cF
    @20
    wcel
    @6
    @21
    @1
    cn
    cF
    @0
    cle
    cr
    cr
    reex
    reex
    xpex
    inex2
    nnex
    elmap
    @19
    @6
    vf
    cF
    @20
    @7
    cF
    wceq
    #
    @11
    @19
    @6
    @22
    @18
    @11
    @22
    cxr
    @12
    @17
    clt
    @22
    cS
    @16
    @22
    cS
    caddc
    @14
    cF
    ccom
    #
    c1
    cseq
    @16
    ovolval.2
    @22
    @23
    @15
    caddc
    c1
    @22
    cF
    @7
    @14
    @22
    @7
    cF
    @22
    id
    eqcomd
    coeq2d
    seqeq3d
    syl5eq
    rneqd
    supeq1d
    biantrud
    @22
    @10
    @5
    cA
    @22
    @9
    @4
    @22
    @8
    @3
    @7
    cF
    cioo
    coeq2
    rneqd
    unieqd
    sseq2d
    bitr3d
    rspcev
    sylanbr
    vy
    cA
    @13
    vf
    cM
    ovolval.1
    elovolm
    sylibr
end
