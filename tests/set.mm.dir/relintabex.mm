include "cab.mm"
include "cint.mm"
include "wrel.mm"
include "cvv.mm"
include "wcel.mm"
include "wex.mm"
include "wn.mm"
include "wceq.mm"
include "intnex.mm"
include "cv.mm"
include "cxp.mm"
include "c0.mm"
include "0nelxp.mm"
include "0ex.mm"
include "eleq1.mm"
include "notbid.mm"
include "spcev.mm"
include "ax-mp.mm"
include "wss.mm"
include "wa.mm"
include "wrex.mm"
include "nss.mm"
include "df-rex.mm"
include "rexv.mm"
include "3bitr2i.mm"
include "df-rel.mm"
include "xchnxbir.mm"
include "mpbir.mm"
include "releq.mm"
include "mtbiri.mm"
include "sylbi.mm"
include "con4i.mm"
include "intexab.mm"
include "sylibr.mm"

theorem relintabex
  let wph: wff ph
  let vx: setvar x


  assert |- ( Rel |^| { x | ph } -> E. x ph )

  proof
    wph
    vx
    cab
    #
    cint
    #
    wrel
    #
    @1
    cvv
    wcel
    #
    wph
    vx
    wex
    @3
    @2
    @3
    wn
    @1
    cvv
    wceq
    #
    @2
    wn
    @0
    intnex
    @4
    @2
    cvv
    wrel
    #
    @5
    wn
    vx
    cv
    #
    cvv
    cvv
    cxp
    #
    wcel
    #
    wn
    #
    vx
    wex
    #
    c0
    @7
    wcel
    #
    wn
    #
    @10
    cvv
    cvv
    0nelxp
    @9
    @12
    vx
    c0
    0ex
    @6
    c0
    wceq
    @8
    @11
    @6
    c0
    @7
    eleq1
    notbid
    spcev
    ax-mp
    cvv
    @7
    wss
    #
    @10
    @5
    @13
    wn
    @6
    cvv
    wcel
    @9
    wa
    vx
    wex
    @9
    vx
    cvv
    wrex
    @10
    vx
    cvv
    @7
    nss
    @9
    vx
    cvv
    df-rex
    @9
    vx
    rexv
    3bitr2i
    cvv
    df-rel
    xchnxbir
    mpbir
    @1
    cvv
    releq
    mtbiri
    sylbi
    con4i
    wph
    vx
    intexab
    sylibr
end
