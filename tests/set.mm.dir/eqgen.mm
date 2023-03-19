include "cv.mm"
include "cec.mm"
include "cen.mm"
include "wbr.mm"
include "csubg.mm"
include "cfv.mm"
include "wcel.mm"
include "cqs.mm"
include "eqid.mm"
include "breq2.mm"
include "wa.mm"
include "cplusg.mm"
include "co.mm"
include "cmpt.mm"
include "cima.mm"
include "cvv.mm"
include "cres.mm"
include "wf1o.mm"
include "simpl.mm"
include "cgrp.mm"
include "wss.mm"
include "wceq.mm"
include "subgrcl.mm"
include "subgss.mm"
include "jca.mm"
include "eqglact.mm"
include "3expa.mm"
include "sylan.mm"
include "cqg.mm"
include "ovex.mm"
include "eqeltri.mm"
include "ecexg.mm"
include "ax-mp.mm"
include "syl6eqelr.mm"
include "wf1.mm"
include "grplactf1o.mm"
include "wb.mm"
include "grplactfval.mm"
include "adantl.mm"
include "f1oeq1.mm"
include "syl.mm"
include "mpbid.mm"
include "f1of1.mm"
include "adantr.mm"
include "f1ores.mm"
include "syl2anc.mm"
include "f1oen2g.mm"
include "syl3anc.mm"
include "breqtrrd.mm"
include "ectocld.mm"

theorem eqgen
  let cA: class A
  let c.sm: class .~
  let cG: class G
  let cX: class X
  let cY: class Y
  let vg: setvar g
  let vx: setvar x
  let c.pl: class .+
  let vy: setvar y
  let vz: setvar z
  let c.0: class .0.
  assume eqger.x: |- X = ( Base ` G )
  assume eqger.r: |- .~ = ( G ~QG Y )


  assert |- ( ( Y e. ( SubGrp ` G ) /\ A e. ( X /. .~ ) ) -> Y ~~ A )

  proof
    cY
    vx
    cv
    #
    c.sm
    cec
    #
    cen
    wbr
    cY
    cA
    cen
    wbr
    cY
    cG
    csubg
    cfv
    #
    wcel
    #
    vx
    cA
    cX
    c.sm
    cX
    c.sm
    cqs
    #
    @4
    eqid
    @1
    cA
    cY
    cen
    breq2
    @3
    @0
    cX
    wcel
    #
    wa
    #
    cY
    vz
    cX
    @0
    vz
    cv
    #
    cG
    cplusg
    cfv
    #
    co
    cmpt
    #
    cY
    cima
    #
    @1
    cen
    @6
    @3
    @10
    cvv
    wcel
    cY
    @10
    @9
    cY
    cres
    #
    wf1o
    #
    cY
    @10
    cen
    wbr
    @3
    @5
    simpl
    @6
    @10
    @1
    cvv
    @3
    cG
    cgrp
    wcel
    #
    cY
    cX
    wss
    #
    wa
    @5
    @1
    @10
    wceq
    #
    @3
    @13
    @14
    cY
    cG
    subgrcl
    #
    cX
    cY
    cG
    eqger.x
    subgss
    #
    jca
    @13
    @14
    @5
    @15
    vz
    @0
    @8
    c.sm
    cG
    cX
    cY
    eqger.x
    eqger.r
    @8
    eqid
    #
    eqglact
    3expa
    sylan
    #
    c.sm
    cvv
    wcel
    @1
    cvv
    wcel
    c.sm
    cG
    cY
    cqg
    co
    cvv
    eqger.r
    cG
    cY
    cqg
    ovex
    eqeltri
    @0
    cvv
    c.sm
    ecexg
    ax-mp
    syl6eqelr
    @6
    cX
    cX
    @9
    wf1
    #
    @14
    @12
    @6
    cX
    cX
    @9
    wf1o
    #
    @20
    @3
    @13
    @5
    @21
    @16
    @13
    @5
    wa
    #
    cX
    cX
    @0
    vy
    cX
    vz
    cX
    vy
    cv
    @7
    @8
    co
    cmpt
    cmpt
    #
    cfv
    #
    wf1o
    #
    @21
    @0
    @8
    vy
    @23
    cG
    cX
    vz
    @23
    eqid
    #
    eqger.x
    @18
    grplactf1o
    @22
    @24
    @9
    wceq
    #
    @25
    @21
    wb
    @5
    @27
    @13
    @0
    @8
    vy
    @23
    cG
    cX
    vz
    @26
    eqger.x
    grplactfval
    adantl
    cX
    cX
    @24
    @9
    f1oeq1
    syl
    mpbid
    sylan
    cX
    cX
    @9
    f1of1
    syl
    @3
    @14
    @5
    @17
    adantr
    cX
    cX
    cY
    @9
    f1ores
    syl2anc
    cY
    @10
    @11
    @2
    cvv
    f1oen2g
    syl3anc
    @19
    breqtrrd
    ectocld
end
