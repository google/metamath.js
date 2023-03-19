include "cv.mm"
include "cin.mm"
include "c0.mm"
include "wceq.mm"
include "cfv.mm"
include "wi.mm"
include "cpw.mm"
include "wral.mm"
include "inidm.mm"
include "wcel.mm"
include "0elpw.mm"
include "ineq1.mm"
include "eqeq1d.mm"
include "fveq2.mm"
include "ineq1d.mm"
include "imbi12d.mm"
include "wb.mm"
include "0in.mm"
include "pm5.5.mm"
include "ax-mp.mm"
include "syl6bb.mm"
include "ineq2d.mm"
include "rspc2v.mm"
include "mp2an.mm"
include "syl5eqr.mm"

theorem ntrkbimka
  let vt: setvar t
  let cB: class B
  let cI: class I
  let vs: setvar s

  disjoint B s
  disjoint B t
  disjoint s t
  disjoint I s
  disjoint I t
  assert |- ( A. s e. ~P B A. t e. ~P B ( ( s i^i t ) = (/) -> ( ( I ` s ) i^i ( I ` t ) ) = (/) ) -> ( I ` (/) ) = (/) )

  proof
    vs
    cv
    #
    vt
    cv
    #
    cin
    #
    c0
    wceq
    #
    @0
    cI
    cfv
    #
    @1
    cI
    cfv
    #
    cin
    #
    c0
    wceq
    #
    wi
    #
    vt
    cB
    cpw
    #
    wral
    vs
    @9
    wral
    #
    c0
    cI
    cfv
    #
    @11
    @11
    cin
    #
    c0
    @11
    inidm
    c0
    @9
    wcel
    #
    @13
    @10
    @12
    c0
    wceq
    #
    wi
    cB
    0elpw
    #
    @15
    @8
    @14
    @11
    @5
    cin
    #
    c0
    wceq
    #
    vs
    vt
    c0
    c0
    @9
    @9
    @0
    c0
    wceq
    #
    @8
    c0
    @1
    cin
    #
    c0
    wceq
    #
    @17
    wi
    #
    @17
    @18
    @3
    @20
    @7
    @17
    @18
    @2
    @19
    c0
    @0
    c0
    @1
    ineq1
    eqeq1d
    @18
    @6
    @16
    c0
    @18
    @4
    @11
    @5
    @0
    c0
    cI
    fveq2
    ineq1d
    eqeq1d
    imbi12d
    @20
    @21
    @17
    wb
    @1
    0in
    @20
    @17
    pm5.5
    ax-mp
    syl6bb
    @1
    c0
    wceq
    #
    @16
    @12
    c0
    @22
    @5
    @11
    @11
    @1
    c0
    cI
    fveq2
    ineq2d
    eqeq1d
    rspc2v
    mp2an
    syl5eqr
end
