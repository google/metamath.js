include "cn.mm"
include "wcel.mm"
include "caddc.mm"
include "c1.mm"
include "cseq.mm"
include "cfv.mm"
include "co.mm"
include "cmin.mm"
include "cli.mm"
include "cn0.mm"
include "c2.mm"
include "cv.mm"
include "cmul.mm"
include "cdiv.mm"
include "cexp.mm"
include "cmpt.mm"
include "eqid.mm"
include "stirlinglem7.mm"
include "stirlinglem4.mm"
include "breqtrrd.mm"

theorem stirlinglem9
  let cA: class A
  let cB: class B
  let vk: setvar k
  let vn: setvar n
  let cJ: class J
  let cK: class K
  let cN: class N
  let vx: setvar x
  assume stirlinglem9.1: |- A = ( n e. NN |-> ( ( ! ` n ) / ( ( sqrt ` ( 2 x. n ) ) x. ( ( n / _e ) ^ n ) ) ) )
  assume stirlinglem9.2: |- B = ( n e. NN |-> ( log ` ( A ` n ) ) )
  assume stirlinglem9.3: |- J = ( n e. NN |-> ( ( ( ( 1 + ( 2 x. n ) ) / 2 ) x. ( log ` ( ( n + 1 ) / n ) ) ) - 1 ) )
  assume stirlinglem9.4: |- K = ( k e. NN |-> ( ( 1 / ( ( 2 x. k ) + 1 ) ) x. ( ( 1 / ( ( 2 x. N ) + 1 ) ) ^ ( 2 x. k ) ) ) )

  disjoint k n
  disjoint K n
  disjoint N k
  disjoint N n
  disjoint k x
  assert |- ( N e. NN -> seq 1 ( + , K ) ~~> ( ( B ` N ) - ( B ` ( N + 1 ) ) ) )

  proof
    cN
    cn
    wcel
    caddc
    cK
    c1
    cseq
    cN
    cJ
    cfv
    cN
    cB
    cfv
    cN
    c1
    caddc
    co
    cB
    cfv
    cmin
    co
    cli
    vk
    vn
    vk
    cn0
    c2
    c1
    c2
    vk
    cv
    cmul
    co
    c1
    caddc
    co
    #
    cdiv
    co
    c1
    c2
    cN
    cmul
    co
    c1
    caddc
    co
    cdiv
    co
    @0
    cexp
    co
    cmul
    co
    cmul
    co
    cmpt
    #
    cJ
    cK
    cN
    stirlinglem9.3
    stirlinglem9.4
    @1
    eqid
    stirlinglem7
    cA
    cB
    vn
    cJ
    cN
    stirlinglem9.1
    stirlinglem9.2
    stirlinglem9.3
    stirlinglem4
    breqtrrd
end
