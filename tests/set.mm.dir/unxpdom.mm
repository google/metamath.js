include "cvv.mm"
include "wcel.mm"
include "wa.mm"
include "c1o.mm"
include "csdm.mm"
include "wbr.mm"
include "cun.mm"
include "cxp.mm"
include "cdom.mm"
include "relsdom.mm"
include "brrelex2i.mm"
include "anim12i.mm"
include "cv.mm"
include "wi.mm"
include "wceq.mm"
include "breq2.mm"
include "anbi1d.mm"
include "uneq1.mm"
include "xpeq1.mm"
include "breq12d.mm"
include "imbi12d.mm"
include "anbi2d.mm"
include "uneq2.mm"
include "xpeq2.mm"
include "weq.mm"
include "cif.mm"
include "cop.mm"
include "cmpt.mm"
include "eqid.mm"
include "unxpdomlem3.mm"
include "vtocl2g.mm"
include "mpcom.mm"

theorem unxpdom
  let cA: class A
  let cB: class B
  let vx: setvar x
  let vy: setvar y
  let vt: setvar t
  let vu: setvar u
  let vv: setvar v
  let vw: setvar w
  let vz: setvar z


  assert |- ( ( 1o ~< A /\ 1o ~< B ) -> ( A u. B ) ~<_ ( A X. B ) )

  proof
    cA
    cvv
    wcel
    #
    cB
    cvv
    wcel
    #
    wa
    c1o
    cA
    csdm
    wbr
    #
    c1o
    cB
    csdm
    wbr
    #
    wa
    #
    cA
    cB
    cun
    #
    cA
    cB
    cxp
    #
    cdom
    wbr
    #
    @2
    @0
    @3
    @1
    c1o
    cA
    csdm
    relsdom
    brrelex2i
    c1o
    cB
    csdm
    relsdom
    brrelex2i
    anim12i
    c1o
    vx
    cv
    #
    csdm
    wbr
    #
    c1o
    vy
    cv
    #
    csdm
    wbr
    #
    wa
    #
    @8
    @10
    cun
    #
    @8
    @10
    cxp
    #
    cdom
    wbr
    #
    wi
    @2
    @11
    wa
    #
    cA
    @10
    cun
    #
    cA
    @10
    cxp
    #
    cdom
    wbr
    #
    wi
    @4
    @7
    wi
    vx
    vy
    cA
    cB
    cvv
    cvv
    @8
    cA
    wceq
    #
    @12
    @16
    @15
    @19
    @20
    @9
    @2
    @11
    @8
    cA
    c1o
    csdm
    breq2
    anbi1d
    @20
    @13
    @17
    @14
    @18
    cdom
    @8
    cA
    @10
    uneq1
    @8
    cA
    @10
    xpeq1
    breq12d
    imbi12d
    @10
    cB
    wceq
    #
    @16
    @4
    @19
    @7
    @21
    @11
    @3
    @2
    @10
    cB
    c1o
    csdm
    breq2
    anbi2d
    @21
    @17
    @5
    @18
    @6
    cdom
    @10
    cB
    cA
    uneq2
    @10
    cB
    cA
    xpeq2
    breq12d
    imbi12d
    vz
    vw
    vv
    vu
    vz
    @13
    vz
    cv
    #
    @8
    wcel
    @22
    vz
    vv
    weq
    vw
    cv
    vt
    cv
    cif
    cop
    vz
    vw
    weq
    vu
    cv
    vv
    cv
    cif
    @22
    cop
    cif
    #
    cmpt
    #
    @23
    vt
    vx
    vy
    @24
    eqid
    @23
    eqid
    unxpdomlem3
    vtocl2g
    mpcom
end
