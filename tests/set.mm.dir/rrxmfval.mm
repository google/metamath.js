include "wcel.mm"
include "cv.mm"
include "co.mm"
include "cmpt2.mm"
include "cc0.mm"
include "csupp.mm"
include "cun.mm"
include "cfv.mm"
include "cmin.mm"
include "c2.mm"
include "cexp.mm"
include "csu.mm"
include "csqrt.mm"
include "cxp.mm"
include "wfn.mm"
include "wceq.mm"
include "crrx.mm"
include "cbs.mm"
include "crefld.mm"
include "cmpt.mm"
include "cgsu.mm"
include "eqid.mm"
include "fvex.mm"
include "fnmpt2i.mm"
include "cds.mm"
include "rrxds.mm"
include "syl6reqr.mm"
include "cfsupp.mm"
include "wbr.mm"
include "cr.mm"
include "cmap.mm"
include "crab.mm"
include "rrxbase.mm"
include "sqxpeqd.mm"
include "fneq12d.mm"
include "mpbiri.mm"
include "fnov.mm"
include "sylib.mm"
include "rrxmval.mm"
include "mpt2eq3dva.mm"
include "eqtrd.mm"

theorem rrxmfval
  let cD: class D
  let vf: setvar f
  let vg: setvar g
  let vh: setvar h
  let vk: setvar k
  let cI: class I
  let cV: class V
  let cX: class X
  let cA: class A
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let cF: class F
  let cG: class G
  assume rrxmval.1: |- X = { h e. ( RR ^m I ) | h finSupp 0 }
  assume rrxmval.d: |- D = ( dist ` ( RR^ ` I ) )

  disjoint D f
  disjoint D g
  disjoint f g
  disjoint f h
  disjoint f k
  disjoint g h
  disjoint g k
  disjoint h k
  disjoint I f
  disjoint I g
  disjoint I h
  disjoint I k
  disjoint V f
  disjoint V g
  disjoint V h
  disjoint V k
  disjoint X f
  disjoint X g
  disjoint X k
  disjoint A k
  disjoint D x
  disjoint D y
  disjoint D z
  disjoint f x
  disjoint f y
  disjoint f z
  disjoint g x
  disjoint g y
  disjoint g z
  disjoint x y
  disjoint x z
  disjoint y z
  disjoint F f
  disjoint F g
  disjoint F h
  disjoint F k
  disjoint F x
  disjoint h x
  disjoint k x
  disjoint G f
  disjoint G g
  disjoint G h
  disjoint G k
  disjoint G x
  disjoint I x
  disjoint I y
  disjoint I z
  disjoint h y
  disjoint h z
  disjoint k y
  disjoint k z
  disjoint V x
  disjoint V y
  disjoint V z
  disjoint X x
  disjoint X y
  disjoint X z
  assert |- ( I e. V -> D = ( f e. X , g e. X |-> ( sqrt ` sum_ k e. ( ( f supp 0 ) u. ( g supp 0 ) ) ( ( ( f ` k ) - ( g ` k ) ) ^ 2 ) ) ) )

  proof
    cI
    cV
    wcel
    #
    cD
    vf
    vg
    cX
    cX
    vf
    cv
    #
    vg
    cv
    #
    cD
    co
    #
    cmpt2
    #
    vf
    vg
    cX
    cX
    @1
    cc0
    csupp
    co
    @2
    cc0
    csupp
    co
    cun
    vk
    cv
    #
    @1
    cfv
    @5
    @2
    cfv
    cmin
    co
    c2
    cexp
    co
    vk
    csu
    csqrt
    cfv
    #
    cmpt2
    @0
    cD
    cX
    cX
    cxp
    #
    wfn
    #
    cD
    @4
    wceq
    @0
    @8
    vf
    vg
    cI
    crrx
    cfv
    #
    cbs
    cfv
    #
    @10
    crefld
    vx
    cI
    vx
    cv
    #
    @1
    cfv
    @11
    @2
    cfv
    cmin
    co
    c2
    cexp
    co
    cmpt
    cgsu
    co
    #
    csqrt
    cfv
    #
    cmpt2
    #
    @10
    @10
    cxp
    #
    wfn
    vf
    vg
    @10
    @10
    @13
    @14
    @14
    eqid
    @12
    csqrt
    fvex
    fnmpt2i
    @0
    @7
    @15
    cD
    @14
    @0
    @14
    @9
    cds
    cfv
    cD
    vx
    @10
    vf
    vg
    @9
    cI
    cV
    @9
    eqid
    #
    @10
    eqid
    #
    rrxds
    rrxmval.d
    syl6reqr
    @0
    cX
    @10
    @0
    @10
    vh
    cv
    cc0
    cfsupp
    wbr
    vh
    cr
    cI
    cmap
    co
    crab
    cX
    @10
    vh
    @9
    cI
    cV
    @16
    @17
    rrxbase
    rrxmval.1
    syl6reqr
    sqxpeqd
    fneq12d
    mpbiri
    vf
    vg
    cX
    cX
    cD
    fnov
    sylib
    @0
    vf
    vg
    cX
    cX
    @3
    @6
    cD
    vh
    vk
    @1
    @2
    cI
    cV
    cX
    rrxmval.1
    rrxmval.d
    rrxmval
    mpt2eq3dva
    eqtrd
end
