include "wcel.mm"
include "cvv.mm"
include "wbr.mm"
include "wa.mm"
include "cui.mm"
include "cdm.mm"
include "cfv.mm"
include "elfvdm.mm"
include "eleq2s.mm"
include "elexd.mm"
include "cop.mm"
include "df-br.mm"
include "cdsr.mm"
include "sylbi.mm"
include "adantr.mm"
include "cin.mm"
include "ccnv.mm"
include "csn.mm"
include "cima.mm"
include "cv.mm"
include "coppr.mm"
include "cur.mm"
include "wceq.mm"
include "fveq2.mm"
include "syl6eqr.mm"
include "fveq2d.mm"
include "ineq12d.mm"
include "cnveqd.mm"
include "sneqd.mm"
include "imaeq12d.mm"
include "df-unit.mm"
include "fvex.mm"
include "eqeltri.mm"
include "inex1.mm"
include "cnvex.mm"
include "imaex.mm"
include "fvmpt.mm"
include "syl5eq.mm"
include "eleq2d.mm"
include "wrel.mm"
include "wb.mm"
include "wss.mm"
include "inss1.mm"
include "reldvdsr.mm"
include "relss.mm"
include "mp2.mm"
include "eliniseg2.mm"
include "ax-mp.mm"
include "brin.mm"
include "bitri.mm"
include "syl6bb.mm"
include "pm5.21nii.mm"

theorem isunit
  let c.pa: class .||
  let cR: class R
  let cS: class S
  let cU: class U
  let c.1: class .1.
  let cE: class E
  let cX: class X
  let vr: setvar r
  assume unit.1: |- U = ( Unit ` R )
  assume unit.2: |- .1. = ( 1r ` R )
  assume unit.3: |- .|| = ( ||r ` R )
  assume unit.4: |- S = ( oppR ` R )
  assume unit.5: |- E = ( ||r ` S )


  assert |- ( X e. U <-> ( X .|| .1. /\ X E .1. ) )

  proof
    cX
    cU
    wcel
    #
    cR
    cvv
    wcel
    #
    cX
    c.1
    c.pa
    wbr
    #
    cX
    c.1
    cE
    wbr
    #
    wa
    #
    @0
    cR
    cui
    cdm
    #
    cR
    @5
    wcel
    cX
    cR
    cui
    cfv
    #
    cU
    cX
    cR
    cui
    elfvdm
    unit.1
    eleq2s
    elexd
    @2
    @1
    @3
    @2
    cX
    c.1
    cop
    #
    c.pa
    wcel
    #
    @1
    cX
    c.1
    c.pa
    df-br
    @8
    cR
    cdsr
    cdm
    #
    cR
    @9
    wcel
    @7
    cR
    cdsr
    cfv
    #
    c.pa
    @7
    cR
    cdsr
    elfvdm
    unit.3
    eleq2s
    elexd
    sylbi
    adantr
    @1
    @0
    cX
    c.pa
    cE
    cin
    #
    ccnv
    #
    c.1
    csn
    #
    cima
    #
    wcel
    #
    @4
    @1
    cU
    @14
    cX
    @1
    cU
    @6
    @14
    unit.1
    vr
    cR
    vr
    cv
    #
    cdsr
    cfv
    #
    @16
    coppr
    cfv
    #
    cdsr
    cfv
    #
    cin
    #
    ccnv
    #
    @16
    cur
    cfv
    #
    csn
    #
    cima
    @14
    cvv
    cui
    @16
    cR
    wceq
    #
    @21
    @12
    @23
    @13
    @24
    @20
    @11
    @24
    @17
    c.pa
    @19
    cE
    @24
    @17
    @10
    c.pa
    @16
    cR
    cdsr
    fveq2
    unit.3
    syl6eqr
    @24
    @19
    cS
    cdsr
    cfv
    cE
    @24
    @18
    cS
    cdsr
    @24
    @18
    cR
    coppr
    cfv
    cS
    @16
    cR
    coppr
    fveq2
    unit.4
    syl6eqr
    fveq2d
    unit.5
    syl6eqr
    ineq12d
    cnveqd
    @24
    @22
    c.1
    @24
    @22
    cR
    cur
    cfv
    c.1
    @16
    cR
    cur
    fveq2
    unit.2
    syl6eqr
    sneqd
    imaeq12d
    vr
    df-unit
    @12
    @13
    @11
    c.pa
    cE
    c.pa
    @10
    cvv
    unit.3
    cR
    cdsr
    fvex
    eqeltri
    inex1
    cnvex
    imaex
    fvmpt
    syl5eq
    eleq2d
    @15
    cX
    c.1
    @11
    wbr
    #
    @4
    @11
    wrel
    #
    @15
    @25
    wb
    @11
    c.pa
    wss
    c.pa
    wrel
    @26
    c.pa
    cE
    inss1
    c.pa
    cR
    unit.3
    reldvdsr
    @11
    c.pa
    relss
    mp2
    @11
    c.1
    cX
    eliniseg2
    ax-mp
    cX
    c.1
    c.pa
    cE
    brin
    bitri
    syl6bb
    pm5.21nii
end
