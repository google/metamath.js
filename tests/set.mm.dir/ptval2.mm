include "wcel.mm"
include "ctop.mm"
include "wf.mm"
include "wa.mm"
include "cv.mm"
include "wfn.mm"
include "cfv.mm"
include "wral.mm"
include "cuni.mm"
include "wceq.mm"
include "cdif.mm"
include "cfn.mm"
include "wrex.mm"
include "w3a.mm"
include "cixp.mm"
include "wex.mm"
include "cab.mm"
include "ctg.mm"
include "csn.mm"
include "crn.mm"
include "cun.mm"
include "cfi.mm"
include "ffn.mm"
include "cpt.mm"
include "eqid.mm"
include "ptval.mm"
include "syl5eq.mm"
include "sylan2.mm"
include "cmpt.mm"
include "ccnv.mm"
include "cima.mm"
include "cmpt2.mm"
include "ptbasfi.mm"
include "ptuni.mm"
include "syl6eqr.mm"
include "sneqd.mm"
include "3ad2ant1.mm"
include "mpteq1d.mm"
include "cnveqd.mm"
include "imaeq1d.mm"
include "mpt2eq3dva.mm"
include "rneqd.mm"
include "uneq12d.mm"
include "fveq2d.mm"
include "eqtrd.mm"

theorem ptval2
  let vw: setvar w
  let vu: setvar u
  let cA: class A
  let vk: setvar k
  let cF: class F
  let cG: class G
  let cJ: class J
  let cV: class V
  let cX: class X
  let vg: setvar g
  let vn: setvar n
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  assume ptval2.1: |- J = ( Xt_ ` F )
  assume ptval2.2: |- X = U. J
  assume ptval2.3: |- G = ( k e. A , u e. ( F ` k ) |-> ( `' ( w e. X |-> ( w ` k ) ) " u ) )

  disjoint k u
  disjoint k w
  disjoint A k
  disjoint u w
  disjoint A u
  disjoint A w
  disjoint F k
  disjoint F u
  disjoint F w
  disjoint V k
  disjoint V u
  disjoint V w
  disjoint X w
  disjoint g k
  disjoint g n
  disjoint g u
  disjoint g w
  disjoint g x
  disjoint g y
  disjoint g z
  disjoint A g
  disjoint k n
  disjoint k x
  disjoint k y
  disjoint k z
  disjoint n u
  disjoint n w
  disjoint n x
  disjoint n y
  disjoint n z
  disjoint A n
  disjoint u x
  disjoint u y
  disjoint u z
  disjoint w x
  disjoint w y
  disjoint w z
  disjoint x y
  disjoint x z
  disjoint A x
  disjoint y z
  disjoint A y
  disjoint A z
  disjoint F g
  disjoint F n
  disjoint F x
  disjoint F y
  disjoint F z
  disjoint V g
  disjoint V n
  disjoint V x
  disjoint V y
  disjoint V z
  assert |- ( ( A e. V /\ F : A --> Top ) -> J = ( topGen ` ( fi ` ( { X } u. ran G ) ) ) )

  proof
    cA
    cV
    wcel
    #
    cA
    ctop
    cF
    wf
    #
    wa
    #
    cJ
    vg
    cv
    #
    cA
    wfn
    vy
    cv
    #
    @3
    cfv
    #
    @4
    cF
    cfv
    #
    wcel
    vy
    cA
    wral
    @5
    @6
    cuni
    wceq
    vy
    cA
    vz
    cv
    cdif
    wral
    vz
    cfn
    wrex
    w3a
    vx
    cv
    vy
    cA
    @5
    cixp
    wceq
    wa
    vg
    wex
    vx
    cab
    #
    ctg
    cfv
    #
    cX
    csn
    #
    cG
    crn
    #
    cun
    #
    cfi
    cfv
    #
    ctg
    cfv
    @1
    @0
    cF
    cA
    wfn
    #
    cJ
    @8
    wceq
    cA
    ctop
    cF
    ffn
    @0
    @13
    wa
    cJ
    cF
    cpt
    cfv
    @8
    ptval2.1
    vx
    vy
    vz
    cA
    @7
    vg
    cF
    cV
    @7
    eqid
    #
    ptval
    syl5eq
    sylan2
    @2
    @7
    @12
    ctg
    @2
    @7
    vn
    cA
    vn
    cv
    cF
    cfv
    cuni
    cixp
    #
    csn
    #
    vk
    vu
    cA
    vk
    cv
    #
    cF
    cfv
    #
    vw
    @15
    @17
    vw
    cv
    cfv
    #
    cmpt
    #
    ccnv
    #
    vu
    cv
    #
    cima
    #
    cmpt2
    #
    crn
    #
    cun
    #
    cfi
    cfv
    @12
    vx
    vy
    vz
    vw
    vu
    cA
    @7
    vg
    vk
    vn
    cF
    cV
    @15
    @14
    @15
    eqid
    ptbasfi
    @2
    @26
    @11
    cfi
    @2
    @16
    @9
    @25
    @10
    @2
    @15
    cX
    @2
    @15
    cJ
    cuni
    cX
    vn
    cA
    cF
    cJ
    cV
    ptval2.1
    ptuni
    ptval2.2
    syl6eqr
    #
    sneqd
    @2
    @24
    cG
    @2
    @24
    vk
    vu
    cA
    @18
    vw
    cX
    @19
    cmpt
    #
    ccnv
    #
    @22
    cima
    #
    cmpt2
    cG
    @2
    vk
    vu
    cA
    @18
    @23
    @30
    @2
    @17
    cA
    wcel
    #
    @22
    @18
    wcel
    #
    w3a
    #
    @21
    @29
    @22
    @33
    @20
    @28
    @33
    vw
    @15
    cX
    @19
    @2
    @31
    @15
    cX
    wceq
    @32
    @27
    3ad2ant1
    mpteq1d
    cnveqd
    imaeq1d
    mpt2eq3dva
    ptval2.3
    syl6eqr
    rneqd
    uneq12d
    fveq2d
    eqtrd
    fveq2d
    eqtrd
end
