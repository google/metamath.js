include "ct1.mm"
include "wcel.mm"
include "cconn.mm"
include "c1o.mm"
include "cen.mm"
include "wbr.mm"
include "wn.mm"
include "cperf.mm"
include "wa.mm"
include "cv.mm"
include "csn.mm"
include "wral.mm"
include "wrex.mm"
include "simplr.mm"
include "simprr.mm"
include "c0.mm"
include "wne.mm"
include "vex.mm"
include "snnz.mm"
include "a1i.mm"
include "ccld.mm"
include "cfv.mm"
include "t1sncld.mm"
include "ad2ant2r.mm"
include "connclo.mm"
include "ensn1.mm"
include "syl6eqbrr.mm"
include "rexlimdvaa.mm"
include "con3d.mm"
include "ralnex.mm"
include "syl6ibr.mm"
include "ctop.mm"
include "wb.mm"
include "t1top.mm"
include "adantr.mm"
include "isperf3.mm"
include "baib.mm"
include "syl.mm"
include "sylibrd.mm"
include "3impia.mm"

theorem t1connperf
  let cJ: class J
  let cX: class X
  let vx: setvar x
  assume t1connperf.1: |- X = U. J


  assert |- ( ( J e. Fre /\ J e. Conn /\ -. X ~~ 1o ) -> J e. Perf )

  proof
    cJ
    ct1
    wcel
    #
    cJ
    cconn
    wcel
    #
    cX
    c1o
    cen
    wbr
    #
    wn
    #
    cJ
    cperf
    wcel
    #
    @0
    @1
    wa
    #
    @3
    vx
    cv
    #
    csn
    #
    cJ
    wcel
    #
    wn
    vx
    cX
    wral
    #
    @4
    @5
    @3
    @8
    vx
    cX
    wrex
    #
    wn
    @9
    @5
    @10
    @2
    @5
    @8
    @2
    vx
    cX
    @5
    @6
    cX
    wcel
    #
    @8
    wa
    #
    wa
    #
    cX
    @7
    c1o
    cen
    @13
    @7
    cJ
    cX
    t1connperf.1
    @0
    @1
    @12
    simplr
    @5
    @11
    @8
    simprr
    @7
    c0
    wne
    @13
    @6
    vx
    vex
    #
    snnz
    a1i
    @0
    @11
    @7
    cJ
    ccld
    cfv
    wcel
    @1
    @8
    @6
    cJ
    cX
    t1connperf.1
    t1sncld
    ad2ant2r
    connclo
    @6
    @14
    ensn1
    syl6eqbrr
    rexlimdvaa
    con3d
    @8
    vx
    cX
    ralnex
    syl6ibr
    @5
    cJ
    ctop
    wcel
    #
    @4
    @9
    wb
    @0
    @15
    @1
    cJ
    t1top
    adantr
    @4
    @15
    @9
    vx
    cJ
    cX
    t1connperf.1
    isperf3
    baib
    syl
    sylibrd
    3impia
end
