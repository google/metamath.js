include "c0.mm"
include "cvv.mm"
include "wcel.mm"
include "cc0.mm"
include "cop.mm"
include "csn.mm"
include "wa.mm"
include "cpthson.mm"
include "cfv.mm"
include "co.mm"
include "wbr.mm"
include "cv.mm"
include "wex.mm"
include "0ex.mm"
include "snex.mm"
include "pm3.2i.mm"
include "0pthon1.mm"
include "breq12.mm"
include "spc2egv.mm"
include "mpsyl.mm"

theorem 0pthonv
  let vf: setvar f
  let cG: class G
  let cN: class N
  let cV: class V
  let vp: setvar p
  assume 0pthon.v: |- V = ( Vtx ` G )

  disjoint G f
  disjoint G p
  disjoint f p
  disjoint N f
  disjoint N p
  assert |- ( N e. V -> E. f E. p f ( N ( PathsOn ` G ) N ) p )

  proof
    c0
    cvv
    wcel
    #
    cc0
    cN
    cop
    #
    csn
    #
    cvv
    wcel
    #
    wa
    cN
    cV
    wcel
    c0
    @2
    cN
    cN
    cG
    cpthson
    cfv
    co
    #
    wbr
    #
    vf
    cv
    #
    vp
    cv
    #
    @4
    wbr
    #
    vp
    wex
    vf
    wex
    @0
    @3
    0ex
    @1
    snex
    pm3.2i
    cG
    cN
    cV
    0pthon.v
    0pthon1
    @8
    @5
    vf
    vp
    c0
    @2
    cvv
    cvv
    @6
    c0
    @7
    @2
    @4
    breq12
    spc2egv
    mpsyl
end
