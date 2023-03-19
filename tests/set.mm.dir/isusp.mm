include "cusp.mm"
include "wcel.mm"
include "cvv.mm"
include "cust.mm"
include "cfv.mm"
include "cutop.mm"
include "wceq.mm"
include "wa.mm"
include "elex.mm"
include "wn.mm"
include "c0.mm"
include "csn.mm"
include "wne.mm"
include "0nep0.mm"
include "cbs.mm"
include "fvprc.mm"
include "syl5eq.mm"
include "fveq2d.mm"
include "ust0.mm"
include "syl6eq.mm"
include "eleq2d.mm"
include "cuss.mm"
include "fvex.mm"
include "eqeltri.mm"
include "elsn.mm"
include "syl6bb.mm"
include "eqeq1d.mm"
include "bitrd.mm"
include "necon3bbid.mm"
include "mpbiri.mm"
include "con4i.mm"
include "adantr.mm"
include "cv.mm"
include "ctopn.mm"
include "fveq2.mm"
include "syl6eqr.mm"
include "eleq12d.mm"
include "eqeq12d.mm"
include "anbi12d.mm"
include "df-usp.mm"
include "elab2g.mm"
include "pm5.21nii.mm"

theorem isusp
  let cB: class B
  let cU: class U
  let cJ: class J
  let cW: class W
  let vw: setvar w
  assume isusp.1: |- B = ( Base ` W )
  assume isusp.2: |- U = ( UnifSt ` W )
  assume isusp.3: |- J = ( TopOpen ` W )


  assert |- ( W e. UnifSp <-> ( U e. ( UnifOn ` B ) /\ J = ( unifTop ` U ) ) )

  proof
    cW
    cusp
    wcel
    cW
    cvv
    wcel
    #
    cU
    cB
    cust
    cfv
    #
    wcel
    #
    cJ
    cU
    cutop
    cfv
    #
    wceq
    #
    wa
    #
    cW
    cusp
    elex
    @2
    @0
    @4
    @0
    @2
    @0
    wn
    #
    @2
    wn
    c0
    c0
    csn
    #
    wne
    0nep0
    @6
    @2
    c0
    @7
    @6
    @2
    cU
    @7
    wceq
    #
    c0
    @7
    wceq
    @6
    @2
    cU
    @7
    csn
    #
    wcel
    @8
    @6
    @1
    @9
    cU
    @6
    @1
    c0
    cust
    cfv
    @9
    @6
    cB
    c0
    cust
    @6
    cB
    cW
    cbs
    cfv
    #
    c0
    isusp.1
    cW
    cbs
    fvprc
    syl5eq
    fveq2d
    ust0
    syl6eq
    eleq2d
    cU
    @7
    cU
    cW
    cuss
    cfv
    #
    cvv
    isusp.2
    cW
    cuss
    fvex
    eqeltri
    elsn
    syl6bb
    @6
    cU
    c0
    @7
    @6
    cU
    @11
    c0
    isusp.2
    cW
    cuss
    fvprc
    syl5eq
    eqeq1d
    bitrd
    necon3bbid
    mpbiri
    con4i
    adantr
    vw
    cv
    #
    cuss
    cfv
    #
    @12
    cbs
    cfv
    #
    cust
    cfv
    #
    wcel
    #
    @12
    ctopn
    cfv
    #
    @13
    cutop
    cfv
    #
    wceq
    #
    wa
    @5
    vw
    cW
    cusp
    cvv
    @12
    cW
    wceq
    #
    @16
    @2
    @19
    @4
    @20
    @13
    cU
    @15
    @1
    @20
    @13
    @11
    cU
    @12
    cW
    cuss
    fveq2
    isusp.2
    syl6eqr
    #
    @20
    @14
    cB
    cust
    @20
    @14
    @10
    cB
    @12
    cW
    cbs
    fveq2
    isusp.1
    syl6eqr
    fveq2d
    eleq12d
    @20
    @17
    cJ
    @18
    @3
    @20
    @17
    cW
    ctopn
    cfv
    cJ
    @12
    cW
    ctopn
    fveq2
    isusp.3
    syl6eqr
    @20
    @13
    cU
    cutop
    @21
    fveq2d
    eqeq12d
    anbi12d
    vw
    df-usp
    elab2g
    pm5.21nii
end
