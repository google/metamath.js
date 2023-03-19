include "cv.mm"
include "c1st.mm"
include "cfv.mm"
include "cgi.mm"
include "csn.mm"
include "cpridl.mm"
include "wcel.mm"
include "crngo.mm"
include "cprrng.mm"
include "wceq.mm"
include "fveq2.mm"
include "syl6eqr.mm"
include "fveq2d.mm"
include "sneqd.mm"
include "eleq12d.mm"
include "df-prrngo.mm"
include "elrab2.mm"

theorem isprrngo
  let cR: class R
  let cG: class G
  let cZ: class Z
  let vr: setvar r
  assume isprrng.1: |- G = ( 1st ` R )
  assume isprrng.2: |- Z = ( GId ` G )


  assert |- ( R e. PrRing <-> ( R e. RingOps /\ { Z } e. ( PrIdl ` R ) ) )

  proof
    vr
    cv
    #
    c1st
    cfv
    #
    cgi
    cfv
    #
    csn
    #
    @0
    cpridl
    cfv
    #
    wcel
    cZ
    csn
    #
    cR
    cpridl
    cfv
    #
    wcel
    vr
    cR
    crngo
    cprrng
    @0
    cR
    wceq
    #
    @3
    @5
    @4
    @6
    @7
    @2
    cZ
    @7
    @2
    cG
    cgi
    cfv
    cZ
    @7
    @1
    cG
    cgi
    @7
    @1
    cR
    c1st
    cfv
    cG
    @0
    cR
    c1st
    fveq2
    isprrng.1
    syl6eqr
    fveq2d
    isprrng.2
    syl6eqr
    sneqd
    @0
    cR
    cpridl
    fveq2
    eleq12d
    vr
    df-prrngo
    elrab2
end
