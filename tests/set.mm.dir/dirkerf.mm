include "cn.mm"
include "wcel.mm"
include "cr.mm"
include "cfv.mm"
include "wf.mm"
include "cv.mm"
include "c2.mm"
include "cpi.mm"
include "cmul.mm"
include "co.mm"
include "cmo.mm"
include "cc0.mm"
include "wceq.mm"
include "c1.mm"
include "caddc.mm"
include "cdiv.mm"
include "csin.mm"
include "cif.mm"
include "cmpt.mm"
include "wa.mm"
include "dirkerval2.mm"
include "dirkerre.mm"
include "eqeltrrd.mm"
include "eqid.mm"
include "fmptd.mm"
include "dirkerval.mm"
include "feq1d.mm"
include "mpbird.mm"

theorem dirkerf
  let vy: setvar y
  let cD: class D
  let vn: setvar n
  let cN: class N
  let vk: setvar k
  let vx: setvar x
  assume dirkerf.1: |- D = ( n e. NN |-> ( y e. RR |-> if ( ( y mod ( 2 x. _pi ) ) = 0 , ( ( ( 2 x. n ) + 1 ) / ( 2 x. _pi ) ) , ( ( sin ` ( ( n + ( 1 / 2 ) ) x. y ) ) / ( ( 2 x. _pi ) x. ( sin ` ( y / 2 ) ) ) ) ) ) )

  disjoint N y
  disjoint n y
  disjoint k x
  assert |- ( N e. NN -> ( D ` N ) : RR --> RR )

  proof
    cN
    cn
    wcel
    #
    cr
    cr
    cN
    cD
    cfv
    #
    wf
    cr
    cr
    vy
    cr
    vy
    cv
    #
    c2
    cpi
    cmul
    co
    #
    cmo
    co
    cc0
    wceq
    c2
    cN
    cmul
    co
    c1
    caddc
    co
    @3
    cdiv
    co
    cN
    c1
    c2
    cdiv
    co
    caddc
    co
    @2
    cmul
    co
    csin
    cfv
    @3
    @2
    c2
    cdiv
    co
    csin
    cfv
    cmul
    co
    cdiv
    co
    cif
    #
    cmpt
    #
    wf
    @0
    vy
    cr
    @4
    cr
    @5
    @0
    @2
    cr
    wcel
    wa
    @2
    @1
    cfv
    @4
    cr
    cD
    @2
    vn
    cN
    vy
    dirkerf.1
    dirkerval2
    cD
    @2
    vn
    cN
    vy
    dirkerf.1
    dirkerre
    eqeltrrd
    @5
    eqid
    fmptd
    @0
    cr
    cr
    @1
    @5
    cD
    vn
    cN
    vy
    dirkerf.1
    dirkerval
    feq1d
    mpbird
end
