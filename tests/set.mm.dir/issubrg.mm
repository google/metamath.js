include "csubrg.mm"
include "cfv.mm"
include "wcel.mm"
include "crg.mm"
include "cress.mm"
include "co.mm"
include "wa.mm"
include "wss.mm"
include "cv.mm"
include "cur.mm"
include "cbs.mm"
include "cpw.mm"
include "crab.mm"
include "df-subrg.mm"
include "mptrcl.mm"
include "simpll.mm"
include "wceq.mm"
include "fveq2.mm"
include "syl6eqr.mm"
include "pweqd.mm"
include "oveq1.mm"
include "eleq1d.mm"
include "anbi12d.mm"
include "rabeqbidv.mm"
include "cvv.mm"
include "fvex.mm"
include "eqeltri.mm"
include "pwex.mm"
include "rabex.mm"
include "fvmpt.mm"
include "eleq2d.mm"
include "oveq2.mm"
include "eleq2.mm"
include "elrab.mm"
include "elpw2.mm"
include "anbi1i.mm"
include "an12.mm"
include "3bitri.mm"
include "ibar.mm"
include "anbi1d.mm"
include "syl5bb.mm"
include "bitrd.mm"
include "pm5.21nii.mm"

theorem issubrg
  let cA: class A
  let cB: class B
  let cR: class R
  let c.1: class .1.
  let vs: setvar s
  let vr: setvar r
  assume issubrg.b: |- B = ( Base ` R )
  assume issubrg.i: |- .1. = ( 1r ` R )


  assert |- ( A e. ( SubRing ` R ) <-> ( ( R e. Ring /\ ( R |`s A ) e. Ring ) /\ ( A C_ B /\ .1. e. A ) ) )

  proof
    cA
    cR
    csubrg
    cfv
    #
    wcel
    #
    cR
    crg
    wcel
    #
    @2
    cR
    cA
    cress
    co
    #
    crg
    wcel
    #
    wa
    #
    cA
    cB
    wss
    #
    c.1
    cA
    wcel
    #
    wa
    #
    wa
    #
    vr
    crg
    vr
    cv
    #
    vs
    cv
    #
    cress
    co
    #
    crg
    wcel
    #
    @10
    cur
    cfv
    #
    @11
    wcel
    #
    wa
    #
    vs
    @10
    cbs
    cfv
    #
    cpw
    #
    crab
    #
    csubrg
    cA
    cR
    vr
    vs
    df-subrg
    #
    mptrcl
    @2
    @4
    @8
    simpll
    @2
    @1
    cA
    cR
    @11
    cress
    co
    #
    crg
    wcel
    #
    c.1
    @11
    wcel
    #
    wa
    #
    vs
    cB
    cpw
    #
    crab
    #
    wcel
    #
    @9
    @2
    @0
    @26
    cA
    vr
    cR
    @19
    @26
    crg
    csubrg
    @10
    cR
    wceq
    #
    @16
    @24
    vs
    @18
    @25
    @28
    @17
    cB
    @28
    @17
    cR
    cbs
    cfv
    #
    cB
    @10
    cR
    cbs
    fveq2
    issubrg.b
    syl6eqr
    pweqd
    @28
    @13
    @22
    @15
    @23
    @28
    @12
    @21
    crg
    @10
    cR
    @11
    cress
    oveq1
    eleq1d
    @28
    @14
    c.1
    @11
    @28
    @14
    cR
    cur
    cfv
    c.1
    @10
    cR
    cur
    fveq2
    issubrg.i
    syl6eqr
    eleq1d
    anbi12d
    rabeqbidv
    @20
    @24
    vs
    @25
    cB
    cB
    @29
    cvv
    issubrg.b
    cR
    cbs
    fvex
    eqeltri
    #
    pwex
    rabex
    fvmpt
    eleq2d
    @27
    @4
    @8
    wa
    #
    @2
    @9
    @27
    cA
    @25
    wcel
    #
    @4
    @7
    wa
    #
    wa
    @6
    @33
    wa
    @31
    @24
    @33
    vs
    cA
    @25
    @11
    cA
    wceq
    #
    @22
    @4
    @23
    @7
    @34
    @21
    @3
    crg
    @11
    cA
    cR
    cress
    oveq2
    eleq1d
    @11
    cA
    c.1
    eleq2
    anbi12d
    elrab
    @32
    @6
    @33
    cA
    cB
    @30
    elpw2
    anbi1i
    @6
    @4
    @7
    an12
    3bitri
    @2
    @4
    @5
    @8
    @2
    @4
    ibar
    anbi1d
    syl5bb
    bitrd
    pm5.21nii
end
