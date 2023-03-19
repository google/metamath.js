include "cperf.mm"
include "wcel.mm"
include "ctop.mm"
include "clp.mm"
include "cfv.mm"
include "wss.mm"
include "wa.mm"
include "cv.mm"
include "csn.mm"
include "wn.mm"
include "wral.mm"
include "isperf2.mm"
include "dfss3.mm"
include "maxlp.mm"
include "baibd.mm"
include "ralbidva.mm"
include "syl5bb.mm"
include "pm5.32i.mm"
include "bitri.mm"

theorem isperf3
  let vx: setvar x
  let cJ: class J
  let cX: class X
  let vj: setvar j
  let vn: setvar n
  let vy: setvar y
  let cP: class P
  let cS: class S
  let cT: class T
  assume lpfval.1: |- X = U. J

  disjoint J x
  disjoint X x
  disjoint j n
  disjoint j x
  disjoint j y
  disjoint J j
  disjoint n x
  disjoint n y
  disjoint J n
  disjoint x y
  disjoint J y
  disjoint P n
  disjoint P x
  disjoint P y
  disjoint S n
  disjoint S x
  disjoint S y
  disjoint T x
  disjoint X j
  disjoint X n
  disjoint X y
  assert |- ( J e. Perf <-> ( J e. Top /\ A. x e. X -. { x } e. J ) )

  proof
    cJ
    cperf
    wcel
    cJ
    ctop
    wcel
    #
    cX
    cX
    cJ
    clp
    cfv
    cfv
    #
    wss
    #
    wa
    @0
    vx
    cv
    #
    csn
    cJ
    wcel
    wn
    #
    vx
    cX
    wral
    #
    wa
    cJ
    cX
    lpfval.1
    isperf2
    @0
    @2
    @5
    @2
    @3
    @1
    wcel
    #
    vx
    cX
    wral
    @0
    @5
    vx
    cX
    @1
    dfss3
    @0
    @6
    @4
    vx
    cX
    @0
    @6
    @3
    cX
    wcel
    @4
    @3
    cJ
    cX
    lpfval.1
    maxlp
    baibd
    ralbidva
    syl5bb
    pm5.32i
    bitri
end
