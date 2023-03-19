include "csrg.mm"
include "wcel.mm"
include "cmnd.mm"
include "cn0.mm"
include "co.mm"
include "wceq.mm"
include "srgmgp.mm"
include "cbs.mm"
include "cfv.mm"
include "eqid.mm"
include "ringidval.mm"
include "mulgnn0z.mm"
include "sylan.mm"

theorem srg1expzeq1
  let cR: class R
  let c.x: class .x.
  let c.1: class .1.
  let cG: class G
  let cN: class N
  assume srg1expzeq1.g: |- G = ( mulGrp ` R )
  assume srg1expzeq1.t: |- .x. = ( .g ` G )
  assume srg1expzeq1.1: |- .1. = ( 1r ` R )


  assert |- ( ( R e. SRing /\ N e. NN0 ) -> ( N .x. .1. ) = .1. )

  proof
    cR
    csrg
    wcel
    cG
    cmnd
    wcel
    cN
    cn0
    wcel
    cN
    c.1
    c.x
    co
    c.1
    wceq
    cR
    cG
    srg1expzeq1.g
    srgmgp
    cG
    cbs
    cfv
    #
    c.x
    cG
    cN
    c.1
    @0
    eqid
    srg1expzeq1.t
    cR
    c.1
    cG
    srg1expzeq1.g
    srg1expzeq1.1
    ringidval
    mulgnn0z
    sylan
end
