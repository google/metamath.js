include "wcel.mm"
include "cvv.mm"
include "cconcat.mm"
include "co.mm"
include "cc0.mm"
include "chash.mm"
include "cfv.mm"
include "caddc.mm"
include "cfzo.mm"
include "cv.mm"
include "cmin.mm"
include "cif.mm"
include "cmpt.mm"
include "wceq.mm"
include "elex.mm"
include "wa.mm"
include "fveq2.mm"
include "oveqan12d.mm"
include "oveq2d.mm"
include "wb.mm"
include "eleq2d.mm"
include "adantr.mm"
include "fveq1.mm"
include "simpr.mm"
include "fveq12d.mm"
include "ifbieq12d.mm"
include "mpteq12dv.mm"
include "df-concat.mm"
include "ovex.mm"
include "mptex.mm"
include "ovmpt2a.mm"
include "syl2an.mm"

theorem ccatfval
  let vx: setvar x
  let cS: class S
  let cT: class T
  let cV: class V
  let cW: class W
  let vs: setvar s
  let vt: setvar t

  disjoint S x
  disjoint T x
  disjoint s t
  disjoint s x
  disjoint S s
  disjoint t x
  disjoint S t
  disjoint T s
  disjoint T t
  assert |- ( ( S e. V /\ T e. W ) -> ( S ++ T ) = ( x e. ( 0 ..^ ( ( # ` S ) + ( # ` T ) ) ) |-> if ( x e. ( 0 ..^ ( # ` S ) ) , ( S ` x ) , ( T ` ( x - ( # ` S ) ) ) ) ) )

  proof
    cS
    cV
    wcel
    cS
    cvv
    wcel
    cT
    cvv
    wcel
    cS
    cT
    cconcat
    co
    vx
    cc0
    cS
    chash
    cfv
    #
    cT
    chash
    cfv
    #
    caddc
    co
    #
    cfzo
    co
    #
    vx
    cv
    #
    cc0
    @0
    cfzo
    co
    #
    wcel
    #
    @4
    cS
    cfv
    #
    @4
    @0
    cmin
    co
    #
    cT
    cfv
    #
    cif
    #
    cmpt
    #
    wceq
    cT
    cW
    wcel
    cS
    cV
    elex
    cT
    cW
    elex
    vs
    vt
    cS
    cT
    cvv
    cvv
    vx
    cc0
    vs
    cv
    #
    chash
    cfv
    #
    vt
    cv
    #
    chash
    cfv
    #
    caddc
    co
    #
    cfzo
    co
    #
    @4
    cc0
    @13
    cfzo
    co
    #
    wcel
    #
    @4
    @12
    cfv
    #
    @4
    @13
    cmin
    co
    #
    @14
    cfv
    #
    cif
    #
    cmpt
    @11
    cconcat
    @12
    cS
    wceq
    #
    @14
    cT
    wceq
    #
    wa
    #
    vx
    @17
    @23
    @3
    @10
    @26
    @16
    @2
    cc0
    cfzo
    @24
    @25
    @13
    @0
    @15
    @1
    caddc
    @12
    cS
    chash
    fveq2
    #
    @14
    cT
    chash
    fveq2
    oveqan12d
    oveq2d
    @26
    @19
    @6
    @20
    @22
    @7
    @9
    @24
    @19
    @6
    wb
    @25
    @24
    @18
    @5
    @4
    @24
    @13
    @0
    cc0
    cfzo
    @27
    oveq2d
    eleq2d
    adantr
    @24
    @20
    @7
    wceq
    @25
    @4
    @12
    cS
    fveq1
    adantr
    @26
    @21
    @8
    @14
    cT
    @24
    @25
    simpr
    @24
    @21
    @8
    wceq
    @25
    @24
    @13
    @0
    @4
    cmin
    @27
    oveq2d
    adantr
    fveq12d
    ifbieq12d
    mpteq12dv
    vx
    vt
    vs
    df-concat
    vx
    @3
    @10
    cc0
    @2
    cfzo
    ovex
    mptex
    ovmpt2a
    syl2an
end
