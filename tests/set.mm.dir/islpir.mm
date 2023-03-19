include "cv.mm"
include "clidl.mm"
include "cfv.mm"
include "clpidl.mm"
include "wceq.mm"
include "crg.mm"
include "clpir.mm"
include "fveq2.mm"
include "eqeq12d.mm"
include "eqeq12i.mm"
include "syl6bbr.mm"
include "df-lpir.mm"
include "elrab2.mm"

theorem islpir
  let cP: class P
  let cR: class R
  let cU: class U
  let vr: setvar r
  let vg: setvar g
  let cB: class B
  let cK: class K
  let cI: class I
  let c.0: class .0.
  assume lpival.p: |- P = ( LPIdeal ` R )
  assume lpiss.u: |- U = ( LIdeal ` R )


  assert |- ( R e. LPIR <-> ( R e. Ring /\ U = P ) )

  proof
    vr
    cv
    #
    clidl
    cfv
    #
    @0
    clpidl
    cfv
    #
    wceq
    #
    cU
    cP
    wceq
    #
    vr
    cR
    crg
    clpir
    @0
    cR
    wceq
    #
    @3
    cR
    clidl
    cfv
    #
    cR
    clpidl
    cfv
    #
    wceq
    @4
    @5
    @1
    @6
    @2
    @7
    @0
    cR
    clidl
    fveq2
    @0
    cR
    clpidl
    fveq2
    eqeq12d
    cU
    @6
    cP
    @7
    lpiss.u
    lpival.p
    eqeq12i
    syl6bbr
    vr
    df-lpir
    elrab2
end
