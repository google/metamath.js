include "cch.mm"
include "wcel.mm"
include "wa.mm"
include "ccv.mm"
include "wbr.mm"
include "wpss.mm"
include "cv.mm"
include "wrex.mm"
include "wn.mm"
include "wceq.mm"
include "eleq1.mm"
include "anbi1d.mm"
include "psseq1.mm"
include "rexbidv.mm"
include "notbid.mm"
include "anbi12d.mm"
include "anbi2d.mm"
include "psseq2.mm"
include "df-cv.mm"
include "brabg.mm"
include "bianabs.mm"

theorem cvbr
  let vx: setvar x
  let cA: class A
  let cB: class B
  let vy: setvar y
  let vz: setvar z
  let cC: class C

  disjoint A x
  disjoint B x
  disjoint x y
  disjoint x z
  disjoint y z
  disjoint A y
  disjoint A z
  disjoint B y
  disjoint B z
  disjoint C x
  assert |- ( ( A e. CH /\ B e. CH ) -> ( A <oH B <-> ( A C. B /\ -. E. x e. CH ( A C. x /\ x C. B ) ) ) )

  proof
    cA
    cch
    wcel
    #
    cB
    cch
    wcel
    #
    wa
    #
    cA
    cB
    ccv
    wbr
    cA
    cB
    wpss
    #
    cA
    vx
    cv
    #
    wpss
    #
    @4
    cB
    wpss
    #
    wa
    #
    vx
    cch
    wrex
    #
    wn
    #
    wa
    #
    vy
    cv
    #
    cch
    wcel
    #
    vz
    cv
    #
    cch
    wcel
    #
    wa
    #
    @11
    @13
    wpss
    #
    @11
    @4
    wpss
    #
    @4
    @13
    wpss
    #
    wa
    #
    vx
    cch
    wrex
    #
    wn
    #
    wa
    #
    wa
    @0
    @14
    wa
    #
    cA
    @13
    wpss
    #
    @5
    @18
    wa
    #
    vx
    cch
    wrex
    #
    wn
    #
    wa
    #
    wa
    @2
    @10
    wa
    vy
    vz
    cA
    cB
    cch
    cch
    ccv
    @11
    cA
    wceq
    #
    @15
    @23
    @22
    @28
    @29
    @12
    @0
    @14
    @11
    cA
    cch
    eleq1
    anbi1d
    @29
    @16
    @24
    @21
    @27
    @11
    cA
    @13
    psseq1
    @29
    @20
    @26
    @29
    @19
    @25
    vx
    cch
    @29
    @17
    @5
    @18
    @11
    cA
    @4
    psseq1
    anbi1d
    rexbidv
    notbid
    anbi12d
    anbi12d
    @13
    cB
    wceq
    #
    @23
    @2
    @28
    @10
    @30
    @14
    @1
    @0
    @13
    cB
    cch
    eleq1
    anbi2d
    @30
    @24
    @3
    @27
    @9
    @13
    cB
    cA
    psseq2
    @30
    @26
    @8
    @30
    @25
    @7
    vx
    cch
    @30
    @18
    @6
    @5
    @13
    cB
    @4
    psseq2
    anbi2d
    rexbidv
    notbid
    anbi12d
    anbi12d
    vy
    vz
    vx
    df-cv
    brabg
    bianabs
end
