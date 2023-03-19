include "csr.mm"
include "wcel.mm"
include "cv.mm"
include "coppr.mm"
include "cfv.mm"
include "crh.mm"
include "co.mm"
include "ccnv.mm"
include "wceq.mm"
include "wa.mm"
include "cstf.mm"
include "wsbc.mm"
include "cab.mm"
include "df-srng.mm"
include "eleq2i.mm"
include "cvv.mm"
include "crg.mm"
include "rhmrcl1.mm"
include "elex.mm"
include "syl.mm"
include "adantr.mm"
include "fvexd.mm"
include "id.mm"
include "fveq2.mm"
include "syl6eqr.mm"
include "sylan9eqr.mm"
include "simpl.mm"
include "fveq2d.mm"
include "oveq12d.mm"
include "eleq12d.mm"
include "cnveqd.mm"
include "eqeq12d.mm"
include "anbi12d.mm"
include "sbcied.mm"
include "elab3.mm"
include "bitri.mm"

theorem issrng
  let cR: class R
  let c.as: class .*
  let cO: class O
  let vi: setvar i
  let vr: setvar r
  assume issrng.o: |- O = ( oppR ` R )
  assume issrng.i: |- .* = ( *rf ` R )


  assert |- ( R e. *Ring <-> ( .* e. ( R RingHom O ) /\ .* = `' .* ) )

  proof
    cR
    csr
    wcel
    cR
    vi
    cv
    #
    vr
    cv
    #
    @1
    coppr
    cfv
    #
    crh
    co
    #
    wcel
    #
    @0
    @0
    ccnv
    #
    wceq
    #
    wa
    #
    vi
    @1
    cstf
    cfv
    #
    wsbc
    #
    vr
    cab
    #
    wcel
    c.as
    cR
    cO
    crh
    co
    #
    wcel
    #
    c.as
    c.as
    ccnv
    #
    wceq
    #
    wa
    #
    csr
    @10
    cR
    vr
    vi
    df-srng
    eleq2i
    @9
    @15
    vr
    cR
    @12
    cR
    cvv
    wcel
    #
    @14
    @12
    cR
    crg
    wcel
    @16
    cR
    cO
    c.as
    rhmrcl1
    cR
    crg
    elex
    syl
    adantr
    @1
    cR
    wceq
    #
    @7
    @15
    vi
    @8
    cvv
    @17
    @1
    cstf
    fvexd
    @17
    @0
    @8
    wceq
    #
    wa
    #
    @4
    @12
    @6
    @14
    @19
    @0
    c.as
    @3
    @11
    @18
    @17
    @0
    @8
    c.as
    @18
    id
    @17
    @8
    cR
    cstf
    cfv
    c.as
    @1
    cR
    cstf
    fveq2
    issrng.i
    syl6eqr
    sylan9eqr
    #
    @19
    @1
    cR
    @2
    cO
    crh
    @17
    @18
    simpl
    #
    @19
    @2
    cR
    coppr
    cfv
    cO
    @19
    @1
    cR
    coppr
    @21
    fveq2d
    issrng.o
    syl6eqr
    oveq12d
    eleq12d
    @19
    @0
    c.as
    @5
    @13
    @20
    @19
    @0
    c.as
    @20
    cnveqd
    eqeq12d
    anbi12d
    sbcied
    elab3
    bitri
end
