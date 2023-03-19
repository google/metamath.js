include "crngo.mm"
include "wcel.mm"
include "wss.mm"
include "cv.mm"
include "cidl.mm"
include "cfv.mm"
include "crab.mm"
include "cint.mm"
include "cvv.mm"
include "cigen.mm"
include "co.mm"
include "wceq.mm"
include "wa.mm"
include "c0.mm"
include "wne.mm"
include "wrex.mm"
include "rngoidl.mm"
include "sseq2.mm"
include "rspcev.mm"
include "sylan.mm"
include "rabn0.mm"
include "sylibr.mm"
include "intex.mm"
include "sylib.mm"
include "cpw.mm"
include "crn.mm"
include "c1st.mm"
include "fvex.mm"
include "eqeltri.mm"
include "rnex.mm"
include "elpw2.mm"
include "simpl.mm"
include "fveq2d.mm"
include "wb.mm"
include "sseq1.mm"
include "adantl.mm"
include "rabeqbidv.mm"
include "inteqd.mm"
include "fveq2.mm"
include "syl6eqr.mm"
include "rneqd.mm"
include "pweqd.mm"
include "df-igen.mm"
include "ovmpt2x.mm"
include "syl3an2br.mm"
include "mpd3an3.mm"

theorem igenval
  let cR: class R
  let cS: class S
  let vj: setvar j
  let cG: class G
  let cX: class X
  let vr: setvar r
  let vs: setvar s
  assume igenval.1: |- G = ( 1st ` R )
  assume igenval.2: |- X = ran G

  disjoint R j
  disjoint S j
  disjoint X j
  disjoint R r
  disjoint R s
  disjoint r s
  disjoint j r
  disjoint j s
  disjoint S r
  disjoint S s
  disjoint X r
  disjoint X s
  assert |- ( ( R e. RingOps /\ S C_ X ) -> ( R IdlGen S ) = |^| { j e. ( Idl ` R ) | S C_ j } )

  proof
    cR
    crngo
    wcel
    #
    cS
    cX
    wss
    #
    cS
    vj
    cv
    #
    wss
    #
    vj
    cR
    cidl
    cfv
    #
    crab
    #
    cint
    #
    cvv
    wcel
    #
    cR
    cS
    cigen
    co
    @6
    wceq
    #
    @0
    @1
    wa
    #
    @5
    c0
    wne
    #
    @7
    @9
    @3
    vj
    @4
    wrex
    #
    @10
    @0
    cX
    @4
    wcel
    @1
    @11
    cR
    cG
    cX
    igenval.1
    igenval.2
    rngoidl
    @3
    @1
    vj
    cX
    @4
    @2
    cX
    cS
    sseq2
    rspcev
    sylan
    @3
    vj
    @4
    rabn0
    sylibr
    @5
    intex
    sylib
    @1
    @0
    cS
    cX
    cpw
    #
    wcel
    @7
    @8
    cS
    cX
    cX
    cG
    crn
    #
    cvv
    igenval.2
    cG
    cG
    cR
    c1st
    cfv
    #
    cvv
    igenval.1
    cR
    c1st
    fvex
    eqeltri
    rnex
    eqeltri
    elpw2
    vr
    vs
    cR
    cS
    crngo
    vr
    cv
    #
    c1st
    cfv
    #
    crn
    #
    cpw
    vs
    cv
    #
    @2
    wss
    #
    vj
    @15
    cidl
    cfv
    #
    crab
    #
    cint
    @6
    cigen
    cvv
    @12
    @15
    cR
    wceq
    #
    @18
    cS
    wceq
    #
    wa
    #
    @21
    @5
    @24
    @19
    @3
    vj
    @20
    @4
    @24
    @15
    cR
    cidl
    @22
    @23
    simpl
    fveq2d
    @23
    @19
    @3
    wb
    @22
    @18
    cS
    @2
    sseq1
    adantl
    rabeqbidv
    inteqd
    @22
    @17
    cX
    @22
    @17
    @13
    cX
    @22
    @16
    cG
    @22
    @16
    @14
    cG
    @15
    cR
    c1st
    fveq2
    igenval.1
    syl6eqr
    rneqd
    igenval.2
    syl6eqr
    pweqd
    vj
    vs
    vr
    df-igen
    ovmpt2x
    syl3an2br
    mpd3an3
end
