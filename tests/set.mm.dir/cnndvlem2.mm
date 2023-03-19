include "cr.mm"
include "ccncf.mm"
include "co.mm"
include "wcel.mm"
include "cdv.mm"
include "cdm.mm"
include "c0.mm"
include "wceq.mm"
include "wa.mm"
include "cv.mm"
include "wex.mm"
include "cnndvlem1.mm"
include "cn0.mm"
include "cfv.mm"
include "csu.mm"
include "cmpt.mm"
include "cvv.mm"
include "reex.mm"
include "mptex.mm"
include "eqeltri.mm"
include "eleq1.mm"
include "oveq2.mm"
include "dmeqd.mm"
include "eqeq1d.mm"
include "anbi12d.mm"
include "spcev.mm"
include "ax-mp.mm"

theorem cnndvlem2
  let vx: setvar x
  let vy: setvar y
  let vw: setvar w
  let cT: class T
  let vf: setvar f
  let vi: setvar i
  let vn: setvar n
  let cF: class F
  let cW: class W
  assume cnndvlem2.t: |- T = ( x e. RR |-> ( abs ` ( ( |_ ` ( x + ( 1 / 2 ) ) ) - x ) ) )
  assume cnndvlem2.f: |- F = ( y e. RR |-> ( n e. NN0 |-> ( ( ( 1 / 2 ) ^ n ) x. ( T ` ( ( ( 2 x. 3 ) ^ n ) x. y ) ) ) ) )
  assume cnndvlem2.w: |- W = ( w e. RR |-> sum_ i e. NN0 ( ( F ` w ) ` i ) )

  disjoint F i
  disjoint F w
  disjoint i w
  disjoint T n
  disjoint T y
  disjoint n y
  disjoint W f
  disjoint i n
  disjoint i y
  disjoint n w
  disjoint w y
  disjoint i x
  disjoint w x
  assert |- E. f ( f e. ( RR -cn-> RR ) /\ dom ( RR _D f ) = (/) )

  proof
    cW
    cr
    cr
    ccncf
    co
    #
    wcel
    #
    cr
    cW
    cdv
    co
    #
    cdm
    #
    c0
    wceq
    #
    wa
    #
    vf
    cv
    #
    @0
    wcel
    #
    cr
    @6
    cdv
    co
    #
    cdm
    #
    c0
    wceq
    #
    wa
    #
    vf
    wex
    vx
    vy
    vw
    cT
    vi
    vn
    cF
    cW
    cnndvlem2.t
    cnndvlem2.f
    cnndvlem2.w
    cnndvlem1
    @11
    @5
    vf
    cW
    cW
    vw
    cr
    cn0
    vi
    cv
    vw
    cv
    cF
    cfv
    cfv
    vi
    csu
    #
    cmpt
    cvv
    cnndvlem2.w
    vw
    cr
    @12
    reex
    mptex
    eqeltri
    @6
    cW
    wceq
    #
    @7
    @1
    @10
    @4
    @6
    cW
    @0
    eleq1
    @13
    @9
    @3
    c0
    @13
    @8
    @2
    @6
    cW
    cr
    cdv
    oveq2
    dmeqd
    eqeq1d
    anbi12d
    spcev
    ax-mp
end
