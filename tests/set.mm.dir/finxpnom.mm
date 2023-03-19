include "com.mm"
include "wcel.mm"
include "wn.mm"
include "cfinxp.mm"
include "cv.mm"
include "c0.mm"
include "cvv.mm"
include "c1o.mm"
include "wceq.mm"
include "wa.mm"
include "cxp.mm"
include "cuni.mm"
include "c1st.mm"
include "cfv.mm"
include "cop.mm"
include "cif.mm"
include "cmpt2.mm"
include "crdg.mm"
include "cab.mm"
include "simpl.mm"
include "con3i.mm"
include "abid.mm"
include "sylnibr.mm"
include "df-finxp.mm"
include "eleq2i.mm"
include "eq0rdv.mm"

theorem finxpnom
  let cU: class U
  let cN: class N
  let vn: setvar n
  let vx: setvar x
  let vy: setvar y


  assert |- ( -. N e. _om -> ( U ^^ N ) = (/) )

  proof
    cN
    com
    wcel
    #
    wn
    #
    vy
    cU
    cN
    cfinxp
    #
    @1
    vy
    cv
    #
    @0
    c0
    cN
    vn
    vx
    com
    cvv
    vn
    cv
    #
    c1o
    wceq
    vx
    cv
    #
    cU
    wcel
    wa
    c0
    @5
    cvv
    cU
    cxp
    wcel
    @4
    cuni
    @5
    c1st
    cfv
    cop
    @4
    @5
    cop
    cif
    cif
    cmpt2
    cN
    @3
    cop
    crdg
    cfv
    wceq
    #
    wa
    #
    vy
    cab
    #
    wcel
    #
    @3
    @2
    wcel
    @1
    @7
    @9
    @7
    @0
    @0
    @6
    simpl
    con3i
    @7
    vy
    abid
    sylnibr
    @2
    @8
    @3
    vx
    vy
    cU
    vn
    cN
    df-finxp
    eleq2i
    sylnibr
    eq0rdv
end
