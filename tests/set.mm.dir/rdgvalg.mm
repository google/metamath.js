include "crdg.mm"
include "cvv.mm"
include "cv.mm"
include "c0.mm"
include "wceq.mm"
include "cdm.mm"
include "wlim.mm"
include "crn.mm"
include "cuni.mm"
include "cfv.mm"
include "cif.mm"
include "cmpt.mm"
include "df-rdg.mm"
include "tfr2a.mm"

theorem rdgvalg
  let cA: class A
  let cB: class B
  let vg: setvar g
  let cF: class F

  disjoint F g
  disjoint A g
  assert |- ( B e. dom rec ( F , A ) -> ( rec ( F , A ) ` B ) = ( ( g e. _V |-> if ( g = (/) , A , if ( Lim dom g , U. ran g , ( F ` ( g ` U. dom g ) ) ) ) ) ` ( rec ( F , A ) |` B ) ) )

  proof
    cB
    cF
    cA
    crdg
    vg
    cvv
    vg
    cv
    #
    c0
    wceq
    cA
    @0
    cdm
    #
    wlim
    @0
    crn
    cuni
    @1
    cuni
    @0
    cfv
    cF
    cfv
    cif
    cif
    cmpt
    vg
    cF
    cA
    df-rdg
    tfr2a
end
