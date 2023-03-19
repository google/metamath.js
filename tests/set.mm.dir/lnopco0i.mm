include "ch0o.mm"
include "wceq.mm"
include "ccom.mm"
include "cnop.mm"
include "cfv.mm"
include "cc0.mm"
include "coeq2.mm"
include "cv.mm"
include "chil.mm"
include "wfn.mm"
include "wral.mm"
include "wb.mm"
include "wf.mm"
include "0lnop.mm"
include "lnopcoi.mm"
include "lnopfi.mm"
include "ffn.mm"
include "ax-mp.mm"
include "ho0f.mm"
include "eqfnfv.mm"
include "mp2an.mm"
include "wcel.mm"
include "c0v.mm"
include "ho0val.mm"
include "fveq2d.mm"
include "lnop0i.mm"
include "syl6eq.mm"
include "hocoi.mm"
include "3eqtr4d.mm"
include "mprgbir.mm"
include "nmlnop0iHIL.mm"
include "3imtr4i.mm"

theorem lnopco0i
  let cS: class S
  let cT: class T
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  assume lnopco.1: |- S e. LinOp
  assume lnopco.2: |- T e. LinOp


  assert |- ( ( normop ` T ) = 0 -> ( normop ` ( S o. T ) ) = 0 )

  proof
    cT
    ch0o
    wceq
    #
    cS
    cT
    ccom
    #
    ch0o
    wceq
    cT
    cnop
    cfv
    cc0
    wceq
    @1
    cnop
    cfv
    cc0
    wceq
    @0
    @1
    cS
    ch0o
    ccom
    #
    ch0o
    cT
    ch0o
    cS
    coeq2
    @2
    ch0o
    wceq
    #
    vx
    cv
    #
    @2
    cfv
    #
    @4
    ch0o
    cfv
    #
    wceq
    #
    vx
    chil
    @2
    chil
    wfn
    #
    ch0o
    chil
    wfn
    #
    @3
    @7
    vx
    chil
    wral
    wb
    chil
    chil
    @2
    wf
    @8
    @2
    cS
    ch0o
    lnopco.1
    0lnop
    lnopcoi
    lnopfi
    chil
    chil
    @2
    ffn
    ax-mp
    chil
    chil
    ch0o
    wf
    @9
    ho0f
    chil
    chil
    ch0o
    ffn
    ax-mp
    vx
    chil
    @2
    ch0o
    eqfnfv
    mp2an
    @4
    chil
    wcel
    #
    @6
    cS
    cfv
    #
    c0v
    @5
    @6
    @10
    @11
    c0v
    cS
    cfv
    c0v
    @10
    @6
    c0v
    cS
    @4
    ho0val
    #
    fveq2d
    cS
    lnopco.1
    lnop0i
    syl6eq
    @4
    cS
    ch0o
    cS
    lnopco.1
    lnopfi
    ho0f
    hocoi
    @12
    3eqtr4d
    mprgbir
    syl6eq
    cT
    lnopco.2
    nmlnop0iHIL
    @1
    cS
    cT
    lnopco.1
    lnopco.2
    lnopcoi
    nmlnop0iHIL
    3imtr4i
end
