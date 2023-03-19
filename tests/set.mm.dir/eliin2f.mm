include "c0.mm"
include "wne.mm"
include "cvv.mm"
include "wcel.mm"
include "ciin.mm"
include "wral.mm"
include "wb.mm"
include "eliin.mm"
include "adantl.mm"
include "wn.mm"
include "wa.mm"
include "prcnel.mm"
include "wrex.mm"
include "cv.mm"
include "csb.mm"
include "wex.mm"
include "n0.mm"
include "biimpi.mm"
include "adantr.mm"
include "wi.mm"
include "a1d.mm"
include "ancld.mm"
include "eximdv.mm"
include "mpd.mm"
include "df-rex.mm"
include "sylibr.mm"
include "nfcv.mm"
include "nfv.mm"
include "nfcsb1v.mm"
include "nfel2.mm"
include "nfn.mm"
include "weq.mm"
include "csbeq1a.mm"
include "eleq2d.mm"
include "notbid.mm"
include "cbvrexf.mm"
include "rexnal.mm"
include "sylib.mm"
include "2falsed.mm"
include "pm2.61dan.mm"

theorem eliin2f
  let vx: setvar x
  let cA: class A
  let cB: class B
  let cC: class C
  let vy: setvar y
  assume eliin2f.1: |- F/_ x B

  disjoint A x
  disjoint A y
  disjoint x y
  disjoint B y
  disjoint C y
  assert |- ( B =/= (/) -> ( A e. |^|_ x e. B C <-> A. x e. B A e. C ) )

  proof
    cB
    c0
    wne
    #
    cA
    cvv
    wcel
    #
    cA
    vx
    cB
    cC
    ciin
    #
    wcel
    #
    cA
    cC
    wcel
    #
    vx
    cB
    wral
    #
    wb
    #
    @1
    @6
    @0
    vx
    cA
    cB
    cC
    cvv
    eliin
    adantl
    @0
    @1
    wn
    #
    wa
    #
    @3
    @5
    @7
    @3
    wn
    @0
    cA
    @2
    prcnel
    adantl
    @8
    @4
    wn
    #
    vx
    cB
    wrex
    #
    @5
    wn
    @8
    cA
    vx
    vy
    cv
    #
    cC
    csb
    #
    wcel
    #
    wn
    #
    vy
    cB
    wrex
    #
    @10
    @8
    @11
    cB
    wcel
    #
    @14
    wa
    #
    vy
    wex
    #
    @15
    @8
    @16
    vy
    wex
    #
    @18
    @0
    @19
    @7
    @0
    @19
    vy
    cB
    n0
    biimpi
    adantr
    @8
    @16
    @17
    vy
    @8
    @16
    @14
    @7
    @16
    @14
    wi
    @0
    @7
    @14
    @16
    cA
    @12
    prcnel
    a1d
    adantl
    ancld
    eximdv
    mpd
    @14
    vy
    cB
    df-rex
    sylibr
    @9
    @14
    vx
    vy
    cB
    eliin2f.1
    vy
    cB
    nfcv
    @9
    vy
    nfv
    @13
    vx
    vx
    cA
    @12
    vx
    @11
    cC
    nfcsb1v
    nfel2
    nfn
    vx
    vy
    weq
    #
    @4
    @13
    @20
    cC
    @12
    cA
    vx
    @11
    cC
    csbeq1a
    eleq2d
    notbid
    cbvrexf
    sylibr
    @4
    vx
    cB
    rexnal
    sylib
    2falsed
    pm2.61dan
end
