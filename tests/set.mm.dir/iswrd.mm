include "cword.mm"
include "wcel.mm"
include "cc0.mm"
include "cv.mm"
include "cfzo.mm"
include "co.mm"
include "wf.mm"
include "cn0.mm"
include "wrex.mm"
include "cab.mm"
include "df-word.mm"
include "eleq2i.mm"
include "cvv.mm"
include "ovex.mm"
include "fex.mm"
include "mpan2.mm"
include "rexlimivw.mm"
include "wceq.mm"
include "feq1.mm"
include "rexbidv.mm"
include "elab3.mm"
include "bitri.mm"

theorem iswrd
  let cS: class S
  let cW: class W
  let vl: setvar l
  let vw: setvar w
  let cV: class V

  disjoint S l
  disjoint W l
  disjoint l w
  disjoint S w
  disjoint V l
  disjoint V w
  disjoint W w
  assert |- ( W e. Word S <-> E. l e. NN0 W : ( 0 ..^ l ) --> S )

  proof
    cW
    cS
    cword
    #
    wcel
    cW
    cc0
    vl
    cv
    #
    cfzo
    co
    #
    cS
    vw
    cv
    #
    wf
    #
    vl
    cn0
    wrex
    #
    vw
    cab
    #
    wcel
    @2
    cS
    cW
    wf
    #
    vl
    cn0
    wrex
    #
    @0
    @6
    cW
    vw
    cS
    vl
    df-word
    eleq2i
    @5
    @8
    vw
    cW
    @7
    cW
    cvv
    wcel
    #
    vl
    cn0
    @7
    @2
    cvv
    wcel
    @9
    cc0
    @1
    cfzo
    ovex
    @2
    cS
    cvv
    cW
    fex
    mpan2
    rexlimivw
    @3
    cW
    wceq
    @4
    @7
    vl
    cn0
    @2
    cS
    @3
    cW
    feq1
    rexbidv
    elab3
    bitri
end
