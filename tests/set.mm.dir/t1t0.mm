include "cuni.mm"
include "ctopon.mm"
include "cfv.mm"
include "wcel.mm"
include "ct1.mm"
include "ct0.mm"
include "ctop.mm"
include "t1top.mm"
include "eqid.mm"
include "toptopon.mm"
include "sylib.mm"
include "wel.mm"
include "wi.mm"
include "wral.mm"
include "weq.mm"
include "wb.mm"
include "biimp.mm"
include "ralimi.mm"
include "imim1i.mm"
include "a1i.mm"
include "ist1-2.mm"
include "ist0-2.mm"
include "3imtr4d.mm"
include "mpcom.mm"

theorem t1t0
  let cJ: class J
  let vf: setvar f
  let vg: setvar g
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D
  let vu: setvar u
  let vv: setvar v
  let vw: setvar w
  let cK: class K
  let vm: setvar m
  let vn: setvar n
  let cF: class F
  let vc: setvar c
  let vd: setvar d
  let vj: setvar j
  let vo: setvar o
  let cU: class U
  let cV: class V
  let cX: class X
  let cY: class Y


  assert |- ( J e. Fre -> J e. Kol2 )

  proof
    cJ
    cJ
    cuni
    #
    ctopon
    cfv
    wcel
    #
    cJ
    ct1
    wcel
    #
    cJ
    ct0
    wcel
    #
    @2
    cJ
    ctop
    wcel
    @1
    cJ
    t1top
    cJ
    @0
    @0
    eqid
    toptopon
    sylib
    @1
    vx
    vo
    wel
    #
    vy
    vo
    wel
    #
    wi
    #
    vo
    cJ
    wral
    #
    vx
    vy
    weq
    #
    wi
    #
    vy
    @0
    wral
    #
    vx
    @0
    wral
    #
    @4
    @5
    wb
    #
    vo
    cJ
    wral
    #
    @8
    wi
    #
    vy
    @0
    wral
    #
    vx
    @0
    wral
    #
    @2
    @3
    @11
    @16
    wi
    @1
    @10
    @15
    vx
    @0
    @9
    @14
    vy
    @0
    @13
    @7
    @8
    @12
    @6
    vo
    cJ
    @4
    @5
    biimp
    ralimi
    imim1i
    ralimi
    ralimi
    a1i
    vx
    vy
    vo
    cJ
    @0
    ist1-2
    vx
    vy
    vo
    cJ
    @0
    ist0-2
    3imtr4d
    mpcom
end
