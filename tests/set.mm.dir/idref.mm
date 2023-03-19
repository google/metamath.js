include "cv.mm"
include "cop.mm"
include "wcel.mm"
include "wral.mm"
include "cmpt.mm"
include "crn.mm"
include "wss.mm"
include "wbr.mm"
include "cid.mm"
include "cres.mm"
include "wf.mm"
include "eqid.mm"
include "fmpt.mm"
include "wfn.mm"
include "opex.mm"
include "fnmpti.mm"
include "df-f.mm"
include "mpbiran.mm"
include "bitri.mm"
include "df-br.mm"
include "ralbii.mm"
include "mptresid.mm"
include "vex.mm"
include "fnasrn.mm"
include "eqtr3i.mm"
include "sseq1i.mm"
include "3bitr4ri.mm"

theorem idref
  let vx: setvar x
  let cA: class A
  let cR: class R

  disjoint A x
  disjoint R x
  assert |- ( ( _I |` A ) C_ R <-> A. x e. A x R x )

  proof
    vx
    cv
    #
    @0
    cop
    #
    cR
    wcel
    #
    vx
    cA
    wral
    #
    vx
    cA
    @1
    cmpt
    #
    crn
    #
    cR
    wss
    #
    @0
    @0
    cR
    wbr
    #
    vx
    cA
    wral
    cid
    cA
    cres
    #
    cR
    wss
    @3
    cA
    cR
    @4
    wf
    #
    @6
    vx
    cA
    cR
    @1
    @4
    @4
    eqid
    #
    fmpt
    @9
    @4
    cA
    wfn
    @6
    vx
    cA
    @1
    @4
    @0
    @0
    opex
    @10
    fnmpti
    cA
    cR
    @4
    df-f
    mpbiran
    bitri
    @7
    @2
    vx
    cA
    @0
    @0
    cR
    df-br
    ralbii
    @8
    @5
    cR
    vx
    cA
    @0
    cmpt
    @8
    @5
    vx
    cA
    mptresid
    vx
    cA
    @0
    vx
    vex
    fnasrn
    eqtr3i
    sseq1i
    3bitr4ri
end
