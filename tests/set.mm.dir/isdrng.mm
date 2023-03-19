include "cv.mm"
include "cui.mm"
include "cfv.mm"
include "cbs.mm"
include "c0g.mm"
include "csn.mm"
include "cdif.mm"
include "wceq.mm"
include "crg.mm"
include "cdr.mm"
include "fveq2.mm"
include "syl6eqr.mm"
include "sneqd.mm"
include "difeq12d.mm"
include "eqeq12d.mm"
include "df-drng.mm"
include "elrab2.mm"

theorem isdrng
  let cB: class B
  let cR: class R
  let cU: class U
  let c.0: class .0.
  let vr: setvar r
  assume isdrng.b: |- B = ( Base ` R )
  assume isdrng.u: |- U = ( Unit ` R )
  assume isdrng.z: |- .0. = ( 0g ` R )


  assert |- ( R e. DivRing <-> ( R e. Ring /\ U = ( B \ { .0. } ) ) )

  proof
    vr
    cv
    #
    cui
    cfv
    #
    @0
    cbs
    cfv
    #
    @0
    c0g
    cfv
    #
    csn
    #
    cdif
    #
    wceq
    cU
    cB
    c.0
    csn
    #
    cdif
    #
    wceq
    vr
    cR
    crg
    cdr
    @0
    cR
    wceq
    #
    @1
    cU
    @5
    @7
    @8
    @1
    cR
    cui
    cfv
    cU
    @0
    cR
    cui
    fveq2
    isdrng.u
    syl6eqr
    @8
    @2
    cB
    @4
    @6
    @8
    @2
    cR
    cbs
    cfv
    cB
    @0
    cR
    cbs
    fveq2
    isdrng.b
    syl6eqr
    @8
    @3
    c.0
    @8
    @3
    cR
    c0g
    cfv
    c.0
    @0
    cR
    c0g
    fveq2
    isdrng.z
    syl6eqr
    sneqd
    difeq12d
    eqeq12d
    vr
    df-drng
    elrab2
end
