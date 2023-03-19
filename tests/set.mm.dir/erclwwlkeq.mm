include "cv.mm"
include "cclwwlk.mm"
include "cfv.mm"
include "wcel.mm"
include "ccsh.mm"
include "co.mm"
include "wceq.mm"
include "cc0.mm"
include "chash.mm"
include "cfz.mm"
include "wrex.mm"
include "w3a.mm"
include "wa.mm"
include "wb.mm"
include "eleq1.mm"
include "adantr.mm"
include "adantl.mm"
include "fveq2.mm"
include "oveq2d.mm"
include "simpl.mm"
include "oveq1.mm"
include "eqeq12d.mm"
include "rexeqbidv.mm"
include "3anbi123d.mm"
include "brabga.mm"

theorem erclwwlkeq
  let vw: setvar w
  let vu: setvar u
  let c.sm: class .~
  let cU: class U
  let vn: setvar n
  let cG: class G
  let cW: class W
  let cX: class X
  let cY: class Y
  assume erclwwlk.r: |- .~ = { <. u , w >. | ( u e. ( ClWWalks ` G ) /\ w e. ( ClWWalks ` G ) /\ E. n e. ( 0 ... ( # ` w ) ) u = ( w cyclShift n ) ) }

  disjoint U n
  disjoint U u
  disjoint U w
  disjoint n u
  disjoint n w
  disjoint u w
  disjoint W n
  disjoint W u
  disjoint W w
  disjoint G n
  disjoint G u
  disjoint G w
  disjoint n u
  disjoint n w
  disjoint u w
  assert |- ( ( U e. X /\ W e. Y ) -> ( U .~ W <-> ( U e. ( ClWWalks ` G ) /\ W e. ( ClWWalks ` G ) /\ E. n e. ( 0 ... ( # ` W ) ) U = ( W cyclShift n ) ) ) )

  proof
    vu
    cv
    #
    cG
    cclwwlk
    cfv
    #
    wcel
    #
    vw
    cv
    #
    @1
    wcel
    #
    @0
    @3
    vn
    cv
    #
    ccsh
    co
    #
    wceq
    #
    vn
    cc0
    @3
    chash
    cfv
    #
    cfz
    co
    #
    wrex
    #
    w3a
    cU
    @1
    wcel
    #
    cW
    @1
    wcel
    #
    cU
    cW
    @5
    ccsh
    co
    #
    wceq
    #
    vn
    cc0
    cW
    chash
    cfv
    #
    cfz
    co
    #
    wrex
    #
    w3a
    vu
    vw
    cU
    cW
    c.sm
    cX
    cY
    @0
    cU
    wceq
    #
    @3
    cW
    wceq
    #
    wa
    #
    @2
    @11
    @4
    @12
    @10
    @17
    @18
    @2
    @11
    wb
    @19
    @0
    cU
    @1
    eleq1
    adantr
    @19
    @4
    @12
    wb
    @18
    @3
    cW
    @1
    eleq1
    adantl
    @20
    @7
    @14
    vn
    @9
    @16
    @19
    @9
    @16
    wceq
    @18
    @19
    @8
    @15
    cc0
    cfz
    @3
    cW
    chash
    fveq2
    oveq2d
    adantl
    @20
    @0
    cU
    @6
    @13
    @18
    @19
    simpl
    @19
    @6
    @13
    wceq
    @18
    @3
    cW
    @5
    ccsh
    oveq1
    adantl
    eqeq12d
    rexeqbidv
    3anbi123d
    erclwwlk.r
    brabga
end
