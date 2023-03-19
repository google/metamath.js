include "wnfc.mm"
include "cvv.mm"
include "wcel.mm"
include "wrex.mm"
include "wsbc.mm"
include "wi.mm"
include "sbcex.mm"
include "a1i.mm"
include "nfnfc1.mm"
include "id.mm"
include "nfcvd.mm"
include "nfeld.mm"
include "cv.mm"
include "2a1i.mm"
include "rexlimd2.mm"
include "wb.mm"
include "wa.mm"
include "wn.mm"
include "wral.mm"
include "sbcng.mm"
include "adantl.mm"
include "sbcralt.mm"
include "ancoms.mm"
include "nfan1.mm"
include "ralbid.mm"
include "bitrd.mm"
include "notbid.mm"
include "dfrex2.mm"
include "sbcbii.mm"
include "3bitr4g.mm"
include "ex.mm"
include "pm5.21ndd.mm"

theorem sbcrext
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
    vy
    cA
    wnfc
    #
    cA
    cvv
    wcel
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
    @3
    @1
    wi
    @0
    @2
    vx
    cA
    sbcex
    a1i
    @0
    @4
    @1
    vy
    cB
    vy
    cA
    nfnfc1
    #
    @0
    vy
    cA
    cvv
    @0
    id
    @0
    vy
    cvv
    nfcvd
    nfeld
    #
    @4
    @1
    wi
    @0
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
    @0
    @1
    @3
    @5
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
    @8
    @12
    @10
    vx
    cA
    wsbc
    #
    wn
    #
    @15
    @1
    @12
    @17
    wb
    @0
    @10
    vx
    cA
    cvv
    sbcng
    adantl
    @8
    @16
    @14
    @8
    @16
    @9
    vx
    cA
    wsbc
    #
    vy
    cB
    wral
    #
    @14
    @1
    @0
    @16
    @19
    wb
    @9
    vx
    vy
    cA
    cB
    cvv
    sbcralt
    ancoms
    @8
    @18
    @13
    vy
    cB
    @0
    @1
    vy
    @6
    @7
    nfan1
    @1
    @18
    @13
    wb
    @0
    wph
    vx
    cA
    cvv
    sbcng
    adantl
    ralbid
    bitrd
    notbid
    bitrd
    @2
    @11
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
    ex
    pm5.21ndd
end
