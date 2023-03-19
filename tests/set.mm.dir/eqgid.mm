include "csubg.mm"
include "cfv.mm"
include "wcel.mm"
include "cec.mm"
include "cv.mm"
include "wbr.mm"
include "wrel.mm"
include "wb.mm"
include "releqg.mm"
include "relelec.mm"
include "ax-mp.mm"
include "cminusg.mm"
include "cplusg.mm"
include "co.mm"
include "wa.mm"
include "cgrp.mm"
include "wceq.mm"
include "subgrcl.mm"
include "adantr.mm"
include "eqid.mm"
include "grpinvid.mm"
include "syl.mm"
include "oveq1d.mm"
include "grplid.mm"
include "sylan.mm"
include "eqtrd.mm"
include "eleq1d.mm"
include "pm5.32da.mm"
include "wss.mm"
include "subgss.mm"
include "grpidcl.mm"
include "w3a.mm"
include "eqgval.mm"
include "3anass.mm"
include "syl6bb.mm"
include "baibd.mm"
include "syl21anc.mm"
include "sseld.mm"
include "pm4.71rd.mm"
include "3bitr4d.mm"
include "syl5bb.mm"
include "eqrdv.mm"

theorem eqgid
  let c.sm: class .~
  let cG: class G
  let cX: class X
  let cY: class Y
  let c.0: class .0.
  let vg: setvar g
  let vx: setvar x
  let c.pl: class .+
  let vy: setvar y
  let vz: setvar z
  let cA: class A
  assume eqger.x: |- X = ( Base ` G )
  assume eqger.r: |- .~ = ( G ~QG Y )
  assume eqgid.3: |- .0. = ( 0g ` G )


  assert |- ( Y e. ( SubGrp ` G ) -> [ .0. ] .~ = Y )

  proof
    cY
    cG
    csubg
    cfv
    wcel
    #
    vx
    c.0
    c.sm
    cec
    #
    cY
    vx
    cv
    #
    @1
    wcel
    #
    c.0
    @2
    c.sm
    wbr
    #
    @0
    @2
    cY
    wcel
    #
    c.sm
    wrel
    @3
    @4
    wb
    c.sm
    cY
    cG
    eqger.r
    releqg
    @2
    c.0
    c.sm
    relelec
    ax-mp
    @0
    @2
    cX
    wcel
    #
    c.0
    cG
    cminusg
    cfv
    #
    cfv
    #
    @2
    cG
    cplusg
    cfv
    #
    co
    #
    cY
    wcel
    #
    wa
    #
    @6
    @5
    wa
    @4
    @5
    @0
    @6
    @11
    @5
    @0
    @6
    wa
    #
    @10
    @2
    cY
    @13
    @10
    c.0
    @2
    @9
    co
    #
    @2
    @13
    @8
    c.0
    @2
    @9
    @13
    cG
    cgrp
    wcel
    #
    @8
    c.0
    wceq
    @0
    @15
    @6
    cY
    cG
    subgrcl
    #
    adantr
    cG
    @7
    c.0
    eqgid.3
    @7
    eqid
    #
    grpinvid
    syl
    oveq1d
    @0
    @15
    @6
    @14
    @2
    wceq
    @16
    cX
    @9
    cG
    @2
    c.0
    eqger.x
    @9
    eqid
    #
    eqgid.3
    grplid
    sylan
    eqtrd
    eleq1d
    pm5.32da
    @0
    @15
    cY
    cX
    wss
    #
    c.0
    cX
    wcel
    #
    @4
    @12
    wb
    @16
    cX
    cY
    cG
    eqger.x
    subgss
    #
    @0
    @15
    @20
    @16
    cX
    cG
    c.0
    eqger.x
    eqgid.3
    grpidcl
    syl
    @15
    @19
    wa
    #
    @4
    @20
    @12
    @22
    @4
    @20
    @6
    @11
    w3a
    @20
    @12
    wa
    c.0
    @2
    @9
    c.sm
    cY
    cG
    @7
    cgrp
    cX
    eqger.x
    @17
    @18
    eqger.r
    eqgval
    @20
    @6
    @11
    3anass
    syl6bb
    baibd
    syl21anc
    @0
    @5
    @6
    @0
    cY
    cX
    @2
    @21
    sseld
    pm4.71rd
    3bitr4d
    syl5bb
    eqrdv
end
