include "cfn.mm"
include "wcel.mm"
include "cfin7.mm"
include "cv.mm"
include "cen.mm"
include "wbr.mm"
include "con0.mm"
include "com.mm"
include "cdif.mm"
include "wrex.mm"
include "wn.mm"
include "wa.mm"
include "wi.mm"
include "eldif.mm"
include "enfi.mm"
include "onfin.mm"
include "sylan9bbr.mm"
include "biimpd.mm"
include "con3d.mm"
include "impancom.mm"
include "sylbi.mm"
include "rexlimiv.mm"
include "con2i.mm"
include "isfin7.mm"
include "mpbird.mm"

theorem fin17
  let cA: class A
  let va: setvar a
  let vb: setvar b
  let vc: setvar c
  let vd: setvar d
  let vf: setvar f
  let vg: setvar g
  let vx: setvar x
  let vy: setvar y
  let cB: class B
  let cV: class V


  assert |- ( A e. Fin -> A e. Fin7 )

  proof
    cA
    cfn
    wcel
    #
    cA
    cfin7
    wcel
    cA
    vb
    cv
    #
    cen
    wbr
    #
    vb
    con0
    com
    cdif
    #
    wrex
    #
    wn
    @4
    @0
    @2
    @0
    wn
    #
    vb
    @3
    @1
    @3
    wcel
    @1
    con0
    wcel
    #
    @1
    com
    wcel
    #
    wn
    #
    wa
    @2
    @5
    wi
    @1
    con0
    com
    eldif
    @6
    @2
    @8
    @5
    @6
    @2
    wa
    #
    @0
    @7
    @9
    @0
    @7
    @2
    @0
    @1
    cfn
    wcel
    @6
    @7
    cA
    @1
    enfi
    @1
    onfin
    sylan9bbr
    biimpd
    con3d
    impancom
    sylbi
    rexlimiv
    con2i
    vb
    cA
    cfn
    isfin7
    mpbird
end
