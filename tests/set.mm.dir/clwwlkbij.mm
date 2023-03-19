include "cv.mm"
include "clsw.mm"
include "cfv.mm"
include "cc0.mm"
include "wceq.mm"
include "cwwlksn.mm"
include "co.mm"
include "crab.mm"
include "cop.mm"
include "csubstr.mm"
include "cmpt.mm"
include "cvv.mm"
include "wcel.mm"
include "cn.mm"
include "cclwwlkn.mm"
include "wf1o.mm"
include "wex.mm"
include "ovex.mm"
include "mptrabex.mm"
include "eqid.mm"
include "clwwlkf1o.mm"
include "f1oeq1.mm"
include "spcegv.mm"
include "mpsyl.mm"

theorem clwwlkbij
  let vw: setvar w
  let vf: setvar f
  let cG: class G
  let cN: class N
  let vx: setvar x

  disjoint G f
  disjoint G w
  disjoint f w
  disjoint N f
  disjoint N w
  disjoint G x
  disjoint f x
  disjoint w x
  disjoint N x
  assert |- ( N e. NN -> E. f f : { w e. ( N WWalksN G ) | ( lastS ` w ) = ( w ` 0 ) } -1-1-onto-> ( N ClWWalksN G ) )

  proof
    vx
    vw
    cv
    #
    clsw
    cfv
    cc0
    @0
    cfv
    wceq
    #
    vw
    cN
    cG
    cwwlksn
    co
    #
    crab
    #
    vx
    cv
    cc0
    cN
    cop
    csubstr
    co
    #
    cmpt
    #
    cvv
    wcel
    cN
    cn
    wcel
    @3
    cN
    cG
    cclwwlkn
    co
    #
    @5
    wf1o
    #
    @3
    @6
    vf
    cv
    #
    wf1o
    #
    vf
    wex
    @1
    vx
    vw
    @2
    @4
    cN
    cG
    cwwlksn
    ovex
    mptrabex
    vw
    vx
    @3
    @5
    cG
    cN
    @3
    eqid
    @5
    eqid
    clwwlkf1o
    @9
    @7
    vf
    @5
    cvv
    @3
    @6
    @8
    @5
    f1oeq1
    spcegv
    mpsyl
end
