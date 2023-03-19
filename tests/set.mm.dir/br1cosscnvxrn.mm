include "wcel.mm"
include "wa.mm"
include "cxrn.mm"
include "cec.mm"
include "cin.mm"
include "c0.mm"
include "wne.mm"
include "cv.mm"
include "wbr.mm"
include "wex.mm"
include "ccnv.mm"
include "ccoss.mm"
include "copab.mm"
include "ecxrn.mm"
include "ineqan12d.mm"
include "inopab.mm"
include "syl6eq.mm"
include "an4.mm"
include "opabbii.mm"
include "neeq1d.mm"
include "opabn0.mm"
include "eeanv.mm"
include "bitri.mm"
include "syl6bb.mm"
include "brcosscnv2.mm"
include "brcosscnv.mm"
include "anbi12d.mm"
include "3bitr4d.mm"

theorem br1cosscnvxrn
  let cA: class A
  let cB: class B
  let cR: class R
  let cS: class S
  let cV: class V
  let cW: class W
  let vx: setvar x
  let vy: setvar y


  assert |- ( ( A e. V /\ B e. W ) -> ( A ,~ `' ( R |X. S ) B <-> ( A ,~ `' R B /\ A ,~ `' S B ) ) )

  proof
    cA
    cV
    wcel
    #
    cB
    cW
    wcel
    #
    wa
    #
    cA
    cR
    cS
    cxrn
    #
    cec
    #
    cB
    @3
    cec
    #
    cin
    #
    c0
    wne
    #
    cA
    vx
    cv
    #
    cR
    wbr
    #
    cB
    @8
    cR
    wbr
    #
    wa
    #
    vx
    wex
    #
    cA
    vy
    cv
    #
    cS
    wbr
    #
    cB
    @13
    cS
    wbr
    #
    wa
    #
    vy
    wex
    #
    wa
    #
    cA
    cB
    @3
    ccnv
    ccoss
    wbr
    cA
    cB
    cR
    ccnv
    ccoss
    wbr
    #
    cA
    cB
    cS
    ccnv
    ccoss
    wbr
    #
    wa
    @2
    @7
    @11
    @16
    wa
    #
    vx
    vy
    copab
    #
    c0
    wne
    #
    @18
    @2
    @6
    @22
    c0
    @2
    @6
    @9
    @14
    wa
    #
    @10
    @15
    wa
    #
    wa
    #
    vx
    vy
    copab
    #
    @22
    @2
    @6
    @24
    vx
    vy
    copab
    #
    @25
    vx
    vy
    copab
    #
    cin
    @27
    @0
    @1
    @4
    @28
    @5
    @29
    vx
    vy
    cA
    cR
    cS
    cV
    ecxrn
    vx
    vy
    cB
    cR
    cS
    cW
    ecxrn
    ineqan12d
    @24
    @25
    vx
    vy
    inopab
    syl6eq
    @26
    @21
    vx
    vy
    @9
    @14
    @10
    @15
    an4
    opabbii
    syl6eq
    neeq1d
    @23
    @21
    vy
    wex
    vx
    wex
    @18
    @21
    vx
    vy
    opabn0
    @11
    @16
    vx
    vy
    eeanv
    bitri
    syl6bb
    cA
    cB
    @3
    cV
    cW
    brcosscnv2
    @2
    @19
    @12
    @20
    @17
    vx
    cA
    cB
    cR
    cV
    cW
    brcosscnv
    vy
    cA
    cB
    cS
    cV
    cW
    brcosscnv
    anbi12d
    3bitr4d
end
