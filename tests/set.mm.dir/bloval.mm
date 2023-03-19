include "cnv.mm"
include "wcel.mm"
include "wa.mm"
include "cblo.mm"
include "co.mm"
include "cv.mm"
include "cfv.mm"
include "cpnf.mm"
include "clt.mm"
include "wbr.mm"
include "crab.mm"
include "cnmoo.mm"
include "clno.mm"
include "wceq.mm"
include "oveq1.mm"
include "fveq1d.mm"
include "breq1d.mm"
include "rabeqbidv.mm"
include "oveq2.mm"
include "syl6eqr.mm"
include "df-blo.mm"
include "cvv.mm"
include "ovex.mm"
include "eqeltri.mm"
include "rabex.mm"
include "ovmpt2.mm"
include "syl5eq.mm"

theorem bloval
  let vt: setvar t
  let cB: class B
  let cU: class U
  let cL: class L
  let cN: class N
  let cW: class W
  let vu: setvar u
  let vw: setvar w
  let cT: class T
  assume bloval.3: |- N = ( U normOpOLD W )
  assume bloval.4: |- L = ( U LnOp W )
  assume bloval.5: |- B = ( U BLnOp W )

  disjoint L t
  disjoint N t
  disjoint U t
  disjoint W t
  disjoint t u
  disjoint t w
  disjoint u w
  disjoint L u
  disjoint L w
  disjoint N u
  disjoint N w
  disjoint T t
  disjoint U u
  disjoint U w
  disjoint W u
  disjoint W w
  assert |- ( ( U e. NrmCVec /\ W e. NrmCVec ) -> B = { t e. L | ( N ` t ) < +oo } )

  proof
    cU
    cnv
    wcel
    cW
    cnv
    wcel
    wa
    cB
    cU
    cW
    cblo
    co
    vt
    cv
    #
    cN
    cfv
    #
    cpnf
    clt
    wbr
    #
    vt
    cL
    crab
    #
    bloval.5
    vu
    vw
    cU
    cW
    cnv
    cnv
    @0
    vu
    cv
    #
    vw
    cv
    #
    cnmoo
    co
    #
    cfv
    #
    cpnf
    clt
    wbr
    #
    vt
    @4
    @5
    clno
    co
    #
    crab
    @3
    cblo
    @0
    cU
    @5
    cnmoo
    co
    #
    cfv
    #
    cpnf
    clt
    wbr
    #
    vt
    cU
    @5
    clno
    co
    #
    crab
    @4
    cU
    wceq
    #
    @8
    @12
    vt
    @9
    @13
    @4
    cU
    @5
    clno
    oveq1
    @14
    @7
    @11
    cpnf
    clt
    @14
    @0
    @6
    @10
    @4
    cU
    @5
    cnmoo
    oveq1
    fveq1d
    breq1d
    rabeqbidv
    @5
    cW
    wceq
    #
    @12
    @2
    vt
    @13
    cL
    @15
    @13
    cU
    cW
    clno
    co
    #
    cL
    @5
    cW
    cU
    clno
    oveq2
    bloval.4
    syl6eqr
    @15
    @11
    @1
    cpnf
    clt
    @15
    @0
    @10
    cN
    @15
    @10
    cU
    cW
    cnmoo
    co
    cN
    @5
    cW
    cU
    cnmoo
    oveq2
    bloval.3
    syl6eqr
    fveq1d
    breq1d
    rabeqbidv
    vw
    vu
    vt
    df-blo
    @2
    vt
    cL
    cL
    @16
    cvv
    bloval.4
    cU
    cW
    clno
    ovex
    eqeltri
    rabex
    ovmpt2
    syl5eq
end
