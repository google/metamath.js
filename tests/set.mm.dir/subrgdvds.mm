include "csubrg.mm"
include "cfv.mm"
include "wcel.mm"
include "wrel.mm"
include "reldvdsr.mm"
include "a1i.mm"
include "cv.mm"
include "wbr.mm"
include "cop.mm"
include "cbs.mm"
include "cmulr.mm"
include "co.mm"
include "wceq.mm"
include "wrex.mm"
include "wa.mm"
include "subrgbas.mm"
include "eqid.mm"
include "subrgss.mm"
include "eqsstr3d.mm"
include "sseld.mm"
include "ressmulr.mm"
include "oveqd.mm"
include "eqeq1d.mm"
include "rexbidv.mm"
include "wss.mm"
include "wi.mm"
include "ssrexv.mm"
include "syl.mm"
include "sylbird.mm"
include "anim12d.mm"
include "dvdsr.mm"
include "3imtr4g.mm"
include "df-br.mm"
include "3imtr3g.mm"
include "relssdv.mm"

theorem subrgdvds
  let cA: class A
  let c.pa: class .||
  let cR: class R
  let cS: class S
  let cE: class E
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  assume subrgdvds.1: |- S = ( R |`s A )
  assume subrgdvds.2: |- .|| = ( ||r ` R )
  assume subrgdvds.3: |- E = ( ||r ` S )


  assert |- ( A e. ( SubRing ` R ) -> E C_ .|| )

  proof
    cA
    cR
    csubrg
    cfv
    #
    wcel
    #
    vx
    vy
    cE
    c.pa
    cE
    wrel
    @1
    cE
    cS
    subrgdvds.3
    reldvdsr
    a1i
    @1
    vx
    cv
    #
    vy
    cv
    #
    cE
    wbr
    #
    @2
    @3
    c.pa
    wbr
    #
    @2
    @3
    cop
    #
    cE
    wcel
    @6
    c.pa
    wcel
    @1
    @2
    cS
    cbs
    cfv
    #
    wcel
    #
    vz
    cv
    #
    @2
    cS
    cmulr
    cfv
    #
    co
    #
    @3
    wceq
    #
    vz
    @7
    wrex
    #
    wa
    @2
    cR
    cbs
    cfv
    #
    wcel
    #
    @9
    @2
    cR
    cmulr
    cfv
    #
    co
    #
    @3
    wceq
    #
    vz
    @14
    wrex
    #
    wa
    @4
    @5
    @1
    @8
    @15
    @13
    @19
    @1
    @7
    @14
    @2
    @1
    @7
    cA
    @14
    cA
    cR
    cS
    subrgdvds.1
    subrgbas
    cA
    @14
    cR
    @14
    eqid
    #
    subrgss
    eqsstr3d
    #
    sseld
    @1
    @13
    @18
    vz
    @7
    wrex
    #
    @19
    @1
    @18
    @12
    vz
    @7
    @1
    @17
    @11
    @3
    @1
    @16
    @10
    @9
    @2
    cA
    cR
    cS
    @16
    @0
    subrgdvds.1
    @16
    eqid
    #
    ressmulr
    oveqd
    eqeq1d
    rexbidv
    @1
    @7
    @14
    wss
    @22
    @19
    wi
    @21
    @18
    vz
    @7
    @14
    ssrexv
    syl
    sylbird
    anim12d
    vz
    @7
    cE
    cS
    @10
    @2
    @3
    @7
    eqid
    subrgdvds.3
    @10
    eqid
    dvdsr
    vz
    @14
    c.pa
    cR
    @16
    @2
    @3
    @20
    subrgdvds.2
    @23
    dvdsr
    3imtr4g
    @2
    @3
    cE
    df-br
    @2
    @3
    c.pa
    df-br
    3imtr3g
    relssdv
end
