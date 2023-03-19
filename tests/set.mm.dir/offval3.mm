include "wcel.mm"
include "wa.mm"
include "cvv.mm"
include "cdm.mm"
include "cin.mm"
include "cv.mm"
include "cfv.mm"
include "co.mm"
include "cmpt.mm"
include "cof.mm"
include "wceq.mm"
include "elex.mm"
include "adantr.mm"
include "adantl.mm"
include "dmexg.mm"
include "inex1g.mm"
include "mptexg.mm"
include "3syl.mm"
include "dmeq.mm"
include "ineqan12d.mm"
include "fveq1.mm"
include "oveqan12d.mm"
include "mpteq12dv.mm"
include "df-of.mm"
include "ovmpt2ga.mm"
include "syl3anc.mm"

theorem offval3
  let vx: setvar x
  let cR: class R
  let cF: class F
  let cG: class G
  let cV: class V
  let cW: class W
  let va: setvar a
  let vb: setvar b
  let cD: class D

  disjoint F x
  disjoint G x
  disjoint V x
  disjoint W x
  disjoint R x
  disjoint F a
  disjoint F b
  disjoint a x
  disjoint b x
  disjoint a b
  disjoint G a
  disjoint G b
  disjoint R a
  disjoint R b
  disjoint D x
  assert |- ( ( F e. V /\ G e. W ) -> ( F oF R G ) = ( x e. ( dom F i^i dom G ) |-> ( ( F ` x ) R ( G ` x ) ) ) )

  proof
    cF
    cV
    wcel
    #
    cG
    cW
    wcel
    #
    wa
    cF
    cvv
    wcel
    #
    cG
    cvv
    wcel
    #
    vx
    cF
    cdm
    #
    cG
    cdm
    #
    cin
    #
    vx
    cv
    #
    cF
    cfv
    #
    @7
    cG
    cfv
    #
    cR
    co
    #
    cmpt
    #
    cvv
    wcel
    #
    cF
    cG
    cR
    cof
    #
    co
    @11
    wceq
    @0
    @2
    @1
    cF
    cV
    elex
    adantr
    @1
    @3
    @0
    cG
    cW
    elex
    adantl
    @0
    @12
    @1
    @0
    @4
    cvv
    wcel
    @6
    cvv
    wcel
    @12
    cF
    cV
    dmexg
    @4
    @5
    cvv
    inex1g
    vx
    @6
    @10
    cvv
    mptexg
    3syl
    adantr
    va
    vb
    cF
    cG
    cvv
    cvv
    vx
    va
    cv
    #
    cdm
    #
    vb
    cv
    #
    cdm
    #
    cin
    #
    @7
    @14
    cfv
    #
    @7
    @16
    cfv
    #
    cR
    co
    #
    cmpt
    @11
    @13
    cvv
    @14
    cF
    wceq
    #
    @16
    cG
    wceq
    #
    wa
    vx
    @18
    @21
    @6
    @10
    @22
    @23
    @15
    @4
    @17
    @5
    @14
    cF
    dmeq
    @16
    cG
    dmeq
    ineqan12d
    @22
    @23
    @19
    @8
    @20
    @9
    cR
    @7
    @14
    cF
    fveq1
    @7
    @16
    cG
    fveq1
    oveqan12d
    mpteq12dv
    vx
    cR
    va
    vb
    df-of
    ovmpt2ga
    syl3anc
end
