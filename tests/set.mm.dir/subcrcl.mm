include "csubc.mm"
include "cfv.mm"
include "wcel.mm"
include "cdm.mm"
include "ccat.mm"
include "cv.mm"
include "chomf.mm"
include "cssc.mm"
include "wbr.mm"
include "ccid.mm"
include "co.mm"
include "cop.mm"
include "cco.mm"
include "wral.mm"
include "wa.mm"
include "wsbc.mm"
include "cab.mm"
include "df-subc.mm"
include "dmmptss.mm"
include "elfvdm.mm"
include "sseldi.mm"

theorem subcrcl
  let cC: class C
  let cH: class H
  let vc: setvar c
  let vf: setvar f
  let vg: setvar g
  let vh: setvar h
  let vj: setvar j
  let vs: setvar s
  let vt: setvar t
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let cJ: class J


  assert |- ( H e. ( Subcat ` C ) -> C e. Cat )

  proof
    cH
    cC
    csubc
    cfv
    wcel
    csubc
    cdm
    ccat
    cC
    vc
    ccat
    vh
    cv
    #
    vc
    cv
    #
    chomf
    cfv
    cssc
    wbr
    vx
    cv
    #
    @1
    ccid
    cfv
    cfv
    @2
    @2
    @0
    co
    wcel
    vg
    cv
    vf
    cv
    @2
    vy
    cv
    #
    cop
    vz
    cv
    #
    @1
    cco
    cfv
    co
    co
    @2
    @4
    @0
    co
    wcel
    vg
    @3
    @4
    @0
    co
    wral
    vf
    @2
    @3
    @0
    co
    wral
    vz
    vs
    cv
    #
    wral
    vy
    @5
    wral
    wa
    vx
    @5
    wral
    vs
    @0
    cdm
    cdm
    wsbc
    wa
    vh
    cab
    csubc
    vx
    vy
    vz
    vf
    vg
    vh
    vs
    vc
    df-subc
    dmmptss
    cH
    cC
    csubc
    elfvdm
    sseldi
end
