include "wcel.mm"
include "wa.mm"
include "cvv.mm"
include "cv.mm"
include "cdm.mm"
include "cin.mm"
include "cfv.mm"
include "co.mm"
include "cmpt.mm"
include "cof.mm"
include "cmpt2.mm"
include "wceq.mm"
include "df-of.mm"
include "a1i.mm"
include "dmeq.mm"
include "ineqan12d.mm"
include "fveq1.mm"
include "oveqan12d.mm"
include "mpteq12dv.mm"
include "adantl.mm"
include "elex.mm"
include "adantr.mm"
include "dmexg.mm"
include "inex1g.mm"
include "mptexg.mm"
include "3syl.mm"
include "ovmpt2d.mm"

theorem offval0
  let vx: setvar x
  let cR: class R
  let cF: class F
  let cG: class G
  let cV: class V
  let cW: class W
  let vf: setvar f
  let vg: setvar g
  let vk: setvar k

  disjoint F x
  disjoint G x
  disjoint R x
  disjoint F f
  disjoint F g
  disjoint f g
  disjoint f x
  disjoint g x
  disjoint G f
  disjoint G g
  disjoint R f
  disjoint R g
  disjoint V f
  disjoint V g
  disjoint W f
  disjoint W g
  disjoint k x
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
    #
    vf
    vg
    cF
    cG
    cvv
    cvv
    vx
    vf
    cv
    #
    cdm
    #
    vg
    cv
    #
    cdm
    #
    cin
    #
    vx
    cv
    #
    @3
    cfv
    #
    @8
    @5
    cfv
    #
    cR
    co
    #
    cmpt
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
    @8
    cF
    cfv
    #
    @8
    cG
    cfv
    #
    cR
    co
    #
    cmpt
    #
    cR
    cof
    #
    cvv
    @20
    vf
    vg
    cvv
    cvv
    @12
    cmpt2
    wceq
    @2
    vx
    cR
    vf
    vg
    df-of
    a1i
    @3
    cF
    wceq
    #
    @5
    cG
    wceq
    #
    wa
    #
    @12
    @19
    wceq
    @2
    @23
    vx
    @7
    @11
    @15
    @18
    @21
    @22
    @4
    @13
    @6
    @14
    @3
    cF
    dmeq
    @5
    cG
    dmeq
    ineqan12d
    @21
    @22
    @9
    @16
    @10
    @17
    cR
    @8
    @3
    cF
    fveq1
    @8
    @5
    cG
    fveq1
    oveqan12d
    mpteq12dv
    adantl
    @0
    cF
    cvv
    wcel
    @1
    cF
    cV
    elex
    adantr
    @1
    cG
    cvv
    wcel
    @0
    cG
    cW
    elex
    adantl
    @2
    @13
    cvv
    wcel
    #
    @15
    cvv
    wcel
    @19
    cvv
    wcel
    @0
    @24
    @1
    cF
    cV
    dmexg
    adantr
    @13
    @14
    cvv
    inex1g
    vx
    @15
    @18
    cvv
    mptexg
    3syl
    ovmpt2d
end
