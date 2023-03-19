include "cv.mm"
include "cress.mm"
include "co.mm"
include "clfig.mm"
include "wcel.mm"
include "clss.mm"
include "cfv.mm"
include "wral.mm"
include "clmod.mm"
include "clnm.mm"
include "wceq.mm"
include "fveq2.mm"
include "syl6eqr.mm"
include "oveq1.mm"
include "eleq1d.mm"
include "raleqbidv.mm"
include "df-lnm.mm"
include "elrab2.mm"

theorem islnm
  let cS: class S
  let vi: setvar i
  let cM: class M
  let vw: setvar w
  assume islnm.s: |- S = ( LSubSp ` M )

  disjoint M i
  disjoint S i
  disjoint i w
  disjoint M w
  disjoint S w
  assert |- ( M e. LNoeM <-> ( M e. LMod /\ A. i e. S ( M |`s i ) e. LFinGen ) )

  proof
    vw
    cv
    #
    vi
    cv
    #
    cress
    co
    #
    clfig
    wcel
    #
    vi
    @0
    clss
    cfv
    #
    wral
    cM
    @1
    cress
    co
    #
    clfig
    wcel
    #
    vi
    cS
    wral
    vw
    cM
    clmod
    clnm
    @0
    cM
    wceq
    #
    @3
    @6
    vi
    @4
    cS
    @7
    @4
    cM
    clss
    cfv
    cS
    @0
    cM
    clss
    fveq2
    islnm.s
    syl6eqr
    @7
    @2
    @5
    clfig
    @0
    cM
    @1
    cress
    oveq1
    eleq1d
    raleqbidv
    vw
    vi
    df-lnm
    elrab2
end
