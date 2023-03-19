include "csubrg.mm"
include "cfv.mm"
include "wcel.mm"
include "cur.mm"
include "cbs.mm"
include "cv.mm"
include "cmulr.mm"
include "co.mm"
include "wceq.mm"
include "wa.mm"
include "wral.mm"
include "eqid.mm"
include "subrg1cl.mm"
include "subrgbas.mm"
include "eleqtrd.mm"
include "subrgss.mm"
include "eqsstr3d.mm"
include "sselda.mm"
include "crg.mm"
include "subrgrcl.mm"
include "ringidmlem.mm"
include "sylan.mm"
include "ressmulr.mm"
include "oveqd.mm"
include "eqeq1d.mm"
include "anbi12d.mm"
include "biimpa.mm"
include "syldan.mm"
include "ralrimiva.mm"
include "wb.mm"
include "subrgring.mm"
include "isringid.mm"
include "syl.mm"
include "mpbi2and.mm"
include "syl6reqr.mm"

theorem subrg1
  let cA: class A
  let cR: class R
  let cS: class S
  let c.1: class .1.
  let vx: setvar x
  assume subrg1.1: |- S = ( R |`s A )
  assume subrg1.2: |- .1. = ( 1r ` R )


  assert |- ( A e. ( SubRing ` R ) -> .1. = ( 1r ` S ) )

  proof
    cA
    cR
    csubrg
    cfv
    #
    wcel
    #
    cS
    cur
    cfv
    #
    cR
    cur
    cfv
    #
    c.1
    @1
    @3
    cS
    cbs
    cfv
    #
    wcel
    #
    @3
    vx
    cv
    #
    cS
    cmulr
    cfv
    #
    co
    #
    @6
    wceq
    #
    @6
    @3
    @7
    co
    #
    @6
    wceq
    #
    wa
    #
    vx
    @4
    wral
    #
    @2
    @3
    wceq
    #
    @1
    @3
    cA
    @4
    cA
    cR
    @3
    @3
    eqid
    #
    subrg1cl
    cA
    cR
    cS
    subrg1.1
    subrgbas
    #
    eleqtrd
    @1
    @12
    vx
    @4
    @1
    @6
    @4
    wcel
    @6
    cR
    cbs
    cfv
    #
    wcel
    #
    @12
    @1
    @4
    @17
    @6
    @1
    @4
    cA
    @17
    @16
    cA
    @17
    cR
    @17
    eqid
    #
    subrgss
    eqsstr3d
    sselda
    @1
    @18
    @3
    @6
    cR
    cmulr
    cfv
    #
    co
    #
    @6
    wceq
    #
    @6
    @3
    @20
    co
    #
    @6
    wceq
    #
    wa
    #
    @12
    @1
    cR
    crg
    wcel
    @18
    @25
    cA
    cR
    subrgrcl
    @17
    cR
    @20
    @3
    @6
    @19
    @20
    eqid
    #
    @15
    ringidmlem
    sylan
    @1
    @25
    @12
    @1
    @22
    @9
    @24
    @11
    @1
    @21
    @8
    @6
    @1
    @20
    @7
    @3
    @6
    cA
    cR
    cS
    @20
    @0
    subrg1.1
    @26
    ressmulr
    #
    oveqd
    eqeq1d
    @1
    @23
    @10
    @6
    @1
    @20
    @7
    @6
    @3
    @27
    oveqd
    eqeq1d
    anbi12d
    biimpa
    syldan
    syldan
    ralrimiva
    @1
    cS
    crg
    wcel
    @5
    @13
    wa
    @14
    wb
    cA
    cR
    cS
    subrg1.1
    subrgring
    vx
    @4
    cS
    @7
    @2
    @3
    @4
    eqid
    @7
    eqid
    @2
    eqid
    isringid
    syl
    mpbi2and
    subrg1.2
    syl6reqr
end
