include "cv.mm"
include "wcel.mm"
include "ccsh.mm"
include "co.mm"
include "wceq.mm"
include "cc0.mm"
include "cfz.mm"
include "wrex.mm"
include "w3a.mm"
include "wa.mm"
include "wb.mm"
include "eleq1.mm"
include "adantr.mm"
include "adantl.mm"
include "simpl.mm"
include "oveq1.mm"
include "eqeq12d.mm"
include "rexbidv.mm"
include "3anbi123d.mm"
include "brabga.mm"

theorem erclwwlkneq
  let vu: setvar u
  let vt: setvar t
  let c.sm: class .~
  let cT: class T
  let cU: class U
  let vn: setvar n
  let cG: class G
  let cN: class N
  let cW: class W
  let cX: class X
  let cY: class Y
  assume erclwwlkn.w: |- W = ( N ClWWalksN G )
  assume erclwwlkn.r: |- .~ = { <. t , u >. | ( t e. W /\ u e. W /\ E. n e. ( 0 ... N ) t = ( u cyclShift n ) ) }

  disjoint N t
  disjoint N u
  disjoint t u
  disjoint T n
  disjoint T t
  disjoint T u
  disjoint n t
  disjoint n u
  disjoint U n
  disjoint U t
  disjoint U u
  disjoint W t
  disjoint W u
  disjoint t u
  assert |- ( ( T e. X /\ U e. Y ) -> ( T .~ U <-> ( T e. W /\ U e. W /\ E. n e. ( 0 ... N ) T = ( U cyclShift n ) ) ) )

  proof
    vt
    cv
    #
    cW
    wcel
    #
    vu
    cv
    #
    cW
    wcel
    #
    @0
    @2
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
    cN
    cfz
    co
    #
    wrex
    #
    w3a
    cT
    cW
    wcel
    #
    cU
    cW
    wcel
    #
    cT
    cU
    @4
    ccsh
    co
    #
    wceq
    #
    vn
    @7
    wrex
    #
    w3a
    vt
    vu
    cT
    cU
    c.sm
    cX
    cY
    @0
    cT
    wceq
    #
    @2
    cU
    wceq
    #
    wa
    #
    @1
    @9
    @3
    @10
    @8
    @13
    @14
    @1
    @9
    wb
    @15
    @0
    cT
    cW
    eleq1
    adantr
    @15
    @3
    @10
    wb
    @14
    @2
    cU
    cW
    eleq1
    adantl
    @16
    @6
    @12
    vn
    @7
    @16
    @0
    cT
    @5
    @11
    @14
    @15
    simpl
    @15
    @5
    @11
    wceq
    @14
    @2
    cU
    @4
    ccsh
    oveq1
    adantl
    eqeq12d
    rexbidv
    3anbi123d
    erclwwlkn.r
    brabga
end
