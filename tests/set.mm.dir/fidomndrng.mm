include "cfn.mm"
include "wcel.mm"
include "cdomn.mm"
include "cdr.mm"
include "wa.mm"
include "crg.mm"
include "cui.mm"
include "cfv.mm"
include "c0g.mm"
include "csn.mm"
include "cdif.mm"
include "wceq.mm"
include "domnring.mm"
include "adantl.mm"
include "cin.mm"
include "c0.mm"
include "wss.mm"
include "wn.mm"
include "cur.mm"
include "cnzr.mm"
include "wne.mm"
include "domnnzr.mm"
include "eqid.mm"
include "nzrnz.mm"
include "syl.mm"
include "neneqd.mm"
include "wb.mm"
include "0unit.mm"
include "mtbird.mm"
include "disjsn.mm"
include "sylibr.mm"
include "unitss.mm"
include "reldisj.mm"
include "ax-mp.mm"
include "sylib.mm"
include "cv.mm"
include "cdsr.mm"
include "wbr.mm"
include "coppr.mm"
include "cmulr.mm"
include "co.mm"
include "cmpt.mm"
include "simplr.mm"
include "simpll.mm"
include "simpr.mm"
include "fidomndrnglem.mm"
include "opprbas.mm"
include "oppr0.mm"
include "oppr1.mm"
include "opprdomn.mm"
include "isunit.mm"
include "sylanbrc.mm"
include "ex.mm"
include "ssrdv.mm"
include "eqssd.mm"
include "isdrng.mm"
include "drngdomn.mm"
include "impbid1.mm"

theorem fidomndrng
  let cB: class B
  let cR: class R
  let vx: setvar x
  let vy: setvar y
  let cA: class A
  let cF: class F
  let wph: wff ph
  let c.x: class .x.
  let c.1: class .1.
  let c.0: class .0.
  assume fidomndrng.b: |- B = ( Base ` R )


  assert |- ( B e. Fin -> ( R e. Domn <-> R e. DivRing ) )

  proof
    cB
    cfn
    wcel
    #
    cR
    cdomn
    wcel
    #
    cR
    cdr
    wcel
    #
    @0
    @1
    @2
    @0
    @1
    wa
    #
    cR
    crg
    wcel
    #
    cR
    cui
    cfv
    #
    cB
    cR
    c0g
    cfv
    #
    csn
    #
    cdif
    #
    wceq
    @2
    @1
    @4
    @0
    cR
    domnring
    adantl
    #
    @3
    @5
    @8
    @3
    @5
    @7
    cin
    c0
    wceq
    #
    @5
    @8
    wss
    #
    @3
    @6
    @5
    wcel
    #
    wn
    @10
    @3
    @12
    cR
    cur
    cfv
    #
    @6
    wceq
    #
    @3
    @13
    @6
    @3
    cR
    cnzr
    wcel
    #
    @13
    @6
    wne
    @1
    @15
    @0
    cR
    domnnzr
    adantl
    cR
    @13
    @6
    @13
    eqid
    #
    @6
    eqid
    #
    nzrnz
    syl
    neneqd
    @3
    @4
    @12
    @14
    wb
    @9
    cR
    @5
    @13
    @6
    @5
    eqid
    #
    @17
    @16
    0unit
    syl
    mtbird
    @5
    @6
    disjsn
    sylibr
    @5
    cB
    wss
    @10
    @11
    wb
    cB
    cR
    @5
    fidomndrng.b
    @18
    unitss
    @5
    @7
    cB
    reldisj
    ax-mp
    sylib
    @3
    vx
    @8
    @5
    @3
    vx
    cv
    #
    @8
    wcel
    #
    @19
    @5
    wcel
    #
    @3
    @20
    wa
    #
    @19
    @13
    cR
    cdsr
    cfv
    #
    wbr
    @19
    @13
    cR
    coppr
    cfv
    #
    cdsr
    cfv
    #
    wbr
    @21
    @22
    vy
    @19
    cB
    @23
    cR
    cR
    cmulr
    cfv
    #
    @13
    vy
    cB
    vy
    cv
    #
    @19
    @26
    co
    cmpt
    #
    @6
    fidomndrng.b
    @17
    @16
    @23
    eqid
    #
    @26
    eqid
    @0
    @1
    @20
    simplr
    #
    @0
    @1
    @20
    simpll
    #
    @3
    @20
    simpr
    #
    @28
    eqid
    fidomndrnglem
    @22
    vy
    @19
    cB
    @25
    @24
    @24
    cmulr
    cfv
    #
    @13
    vy
    cB
    @27
    @19
    @33
    co
    cmpt
    #
    @6
    cB
    cR
    @24
    @24
    eqid
    #
    fidomndrng.b
    opprbas
    cR
    @24
    @6
    @35
    @17
    oppr0
    cR
    @13
    @24
    @35
    @16
    oppr1
    @25
    eqid
    #
    @33
    eqid
    @22
    @1
    @24
    cdomn
    wcel
    @30
    cR
    @24
    @35
    opprdomn
    syl
    @31
    @32
    @34
    eqid
    fidomndrnglem
    @23
    cR
    @24
    @5
    @13
    @25
    @19
    @18
    @16
    @29
    @35
    @36
    isunit
    sylanbrc
    ex
    ssrdv
    eqssd
    cB
    cR
    @5
    @6
    fidomndrng.b
    @18
    @17
    isdrng
    sylanbrc
    ex
    cR
    drngdomn
    impbid1
end
