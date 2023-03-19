include "cv.mm"
include "c1st.mm"
include "cfv.mm"
include "crn.mm"
include "wne.mm"
include "wss.mm"
include "wceq.mm"
include "wo.mm"
include "wi.mm"
include "cidl.mm"
include "wral.mm"
include "wa.mm"
include "crab.mm"
include "crngo.mm"
include "cmaxidl.mm"
include "fveq2.mm"
include "syl6eqr.mm"
include "rneqd.mm"
include "neeq2d.mm"
include "eqeq2d.mm"
include "orbi2d.mm"
include "imbi2d.mm"
include "raleqbidv.mm"
include "anbi12d.mm"
include "rabeqbidv.mm"
include "df-maxidl.mm"
include "fvex.mm"
include "rabex.mm"
include "fvmpt.mm"

theorem maxidlval
  let cR: class R
  let vi: setvar i
  let vj: setvar j
  let cG: class G
  let cX: class X
  let vr: setvar r
  assume maxidlval.1: |- G = ( 1st ` R )
  assume maxidlval.2: |- X = ran G

  disjoint R i
  disjoint R j
  disjoint i j
  disjoint R r
  disjoint i r
  disjoint j r
  disjoint X r
  assert |- ( R e. RingOps -> ( MaxIdl ` R ) = { i e. ( Idl ` R ) | ( i =/= X /\ A. j e. ( Idl ` R ) ( i C_ j -> ( j = i \/ j = X ) ) ) } )

  proof
    vr
    cR
    vi
    cv
    #
    vr
    cv
    #
    c1st
    cfv
    #
    crn
    #
    wne
    #
    @0
    vj
    cv
    #
    wss
    #
    @5
    @0
    wceq
    #
    @5
    @3
    wceq
    #
    wo
    #
    wi
    #
    vj
    @1
    cidl
    cfv
    #
    wral
    #
    wa
    #
    vi
    @11
    crab
    @0
    cX
    wne
    #
    @6
    @7
    @5
    cX
    wceq
    #
    wo
    #
    wi
    #
    vj
    cR
    cidl
    cfv
    #
    wral
    #
    wa
    #
    vi
    @18
    crab
    crngo
    cmaxidl
    @1
    cR
    wceq
    #
    @13
    @20
    vi
    @11
    @18
    @1
    cR
    cidl
    fveq2
    #
    @21
    @4
    @14
    @12
    @19
    @21
    @3
    cX
    @0
    @21
    @3
    cG
    crn
    cX
    @21
    @2
    cG
    @21
    @2
    cR
    c1st
    cfv
    cG
    @1
    cR
    c1st
    fveq2
    maxidlval.1
    syl6eqr
    rneqd
    maxidlval.2
    syl6eqr
    #
    neeq2d
    @21
    @10
    @17
    vj
    @11
    @18
    @22
    @21
    @9
    @16
    @6
    @21
    @8
    @15
    @7
    @21
    @3
    cX
    @5
    @23
    eqeq2d
    orbi2d
    imbi2d
    raleqbidv
    anbi12d
    rabeqbidv
    vi
    vj
    vr
    df-maxidl
    @20
    vi
    @18
    cR
    cidl
    fvex
    rabex
    fvmpt
end
