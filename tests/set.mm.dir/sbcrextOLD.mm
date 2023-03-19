include "cvv.mm"
include "wcel.mm"
include "wnfc.mm"
include "wrex.mm"
include "wsbc.mm"
include "wb.mm"
include "wa.mm"
include "wn.mm"
include "wral.mm"
include "sbcng.mm"
include "adantr.mm"
include "sbcralt.mm"
include "nfnfc1.mm"
include "id.mm"
include "nfcvd.mm"
include "nfeld.mm"
include "nfan1.mm"
include "adantl.mm"
include "ralbid.mm"
include "ancoms.mm"
include "bitrd.mm"
include "notbid.mm"
include "dfrex2.mm"
include "sbcbii.mm"
include "3bitr4g.mm"
include "sbcex.mm"
include "con3i.mm"
include "wi.mm"
include "cv.mm"
include "2a1i.mm"
include "rexlimd2.mm"
include "con3rr3.mm"
include "imp.mm"
include "2falsed.mm"
include "pm2.61ian.mm"

theorem sbcrextOLD
  let wph: wff ph
  let vx: setvar x
  let vy: setvar y
  let cA: class A
  let cB: class B
  let vz: setvar z
  let cV: class V

  disjoint x y
  disjoint B x
  disjoint x z
  disjoint y z
  disjoint A z
  disjoint B z
  disjoint V z
  disjoint ph z
  assert |- ( F/_ y A -> ( [. A / x ]. E. y e. B ph <-> E. y e. B [. A / x ]. ph ) )

  proof
    cA
    cvv
    wcel
    #
    vy
    cA
    wnfc
    #
    wph
    vy
    cB
    wrex
    #
    vx
    cA
    wsbc
    #
    wph
    vx
    cA
    wsbc
    #
    vy
    cB
    wrex
    #
    wb
    @0
    @1
    wa
    #
    wph
    wn
    #
    vy
    cB
    wral
    #
    wn
    #
    vx
    cA
    wsbc
    #
    @4
    wn
    #
    vy
    cB
    wral
    #
    wn
    #
    @3
    @5
    @6
    @10
    @8
    vx
    cA
    wsbc
    #
    wn
    #
    @13
    @0
    @10
    @15
    wb
    @1
    @8
    vx
    cA
    cvv
    sbcng
    adantr
    @6
    @14
    @12
    @6
    @14
    @7
    vx
    cA
    wsbc
    #
    vy
    cB
    wral
    #
    @12
    @7
    vx
    vy
    cA
    cB
    cvv
    sbcralt
    @1
    @0
    @17
    @12
    wb
    @1
    @0
    wa
    @16
    @11
    vy
    cB
    @1
    @0
    vy
    vy
    cA
    nfnfc1
    #
    @1
    vy
    cA
    cvv
    @1
    id
    @1
    vy
    cvv
    nfcvd
    nfeld
    #
    nfan1
    @0
    @16
    @11
    wb
    @1
    wph
    vx
    cA
    cvv
    sbcng
    adantl
    ralbid
    ancoms
    bitrd
    notbid
    bitrd
    @2
    @9
    vx
    cA
    wph
    vy
    cB
    dfrex2
    sbcbii
    @4
    vy
    cB
    dfrex2
    3bitr4g
    @0
    wn
    #
    @1
    wa
    @3
    @5
    @20
    @3
    wn
    @1
    @3
    @0
    @2
    vx
    cA
    sbcex
    con3i
    adantr
    @20
    @1
    @5
    wn
    @1
    @5
    @0
    @1
    @4
    @0
    vy
    cB
    @18
    @19
    @4
    @0
    wi
    @1
    vy
    cv
    cB
    wcel
    wph
    vx
    cA
    sbcex
    2a1i
    rexlimd2
    con3rr3
    imp
    2falsed
    pm2.61ian
end
