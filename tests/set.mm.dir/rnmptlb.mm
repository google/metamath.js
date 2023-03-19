include "cv.mm"
include "cle.mm"
include "wbr.mm"
include "cmpt.mm"
include "crn.mm"
include "wral.mm"
include "cr.mm"
include "wrex.mm"
include "wceq.mm"
include "breq1.mm"
include "ralbidv.mm"
include "cbvrexv.mm"
include "sylib.mm"
include "wcel.mm"
include "wi.mm"
include "wa.mm"
include "cvv.mm"
include "wb.mm"
include "vex.mm"
include "eqid.mm"
include "elrnmpt.mm"
include "ax-mp.mm"
include "biimpi.mm"
include "adantl.mm"
include "nfra1.mm"
include "nfv.mm"
include "w3a.mm"
include "rspa.mm"
include "3adant3.mm"
include "simp3.mm"
include "breqtrrd.mm"
include "3exp.mm"
include "rexlimd.mm"
include "imp.mm"
include "adantll.mm"
include "syldan.mm"
include "ralrimiva.mm"
include "exp31.mm"
include "reximdva.mm"
include "mpd.mm"

theorem rnmptlb
  let wph: wff ph
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let cA: class A
  let cB: class B
  let vw: setvar w
  assume rnmptlb.1: |- ( ph -> E. y e. RR A. x e. A y <_ B )

  disjoint A y
  disjoint A z
  disjoint y z
  disjoint B y
  disjoint B z
  disjoint ph z
  disjoint x y
  disjoint x z
  disjoint A w
  disjoint w y
  disjoint w z
  disjoint B w
  disjoint ph w
  disjoint w x
  assert |- ( ph -> E. y e. RR A. z e. ran ( x e. A |-> B ) y <_ z )

  proof
    wph
    vw
    cv
    #
    vz
    cv
    #
    cle
    wbr
    #
    vz
    vx
    cA
    cB
    cmpt
    #
    crn
    #
    wral
    #
    vw
    cr
    wrex
    #
    vy
    cv
    #
    @1
    cle
    wbr
    #
    vz
    @4
    wral
    #
    vy
    cr
    wrex
    wph
    @0
    cB
    cle
    wbr
    #
    vx
    cA
    wral
    #
    vw
    cr
    wrex
    #
    @6
    wph
    @7
    cB
    cle
    wbr
    #
    vx
    cA
    wral
    #
    vy
    cr
    wrex
    @12
    rnmptlb.1
    @14
    @11
    vy
    vw
    cr
    @7
    @0
    wceq
    @13
    @10
    vx
    cA
    @7
    @0
    cB
    cle
    breq1
    ralbidv
    cbvrexv
    sylib
    wph
    @11
    @5
    vw
    cr
    wph
    @0
    cr
    wcel
    #
    @11
    @5
    wi
    wph
    @15
    @11
    @5
    wph
    @15
    wa
    #
    @11
    wa
    #
    @2
    vz
    @4
    @17
    @1
    @4
    wcel
    #
    @1
    cB
    wceq
    #
    vx
    cA
    wrex
    #
    @2
    @18
    @20
    @17
    @18
    @20
    @1
    cvv
    wcel
    @18
    @20
    wb
    vz
    vex
    vx
    cA
    cB
    @1
    @3
    cvv
    @3
    eqid
    elrnmpt
    ax-mp
    biimpi
    adantl
    @11
    @20
    @2
    @16
    @11
    @20
    @2
    @11
    @19
    @2
    vx
    cA
    @10
    vx
    cA
    nfra1
    @2
    vx
    nfv
    @11
    vx
    cv
    cA
    wcel
    #
    @19
    @2
    @11
    @21
    @19
    w3a
    @0
    cB
    @1
    cle
    @11
    @21
    @10
    @19
    @10
    vx
    cA
    rspa
    3adant3
    @11
    @21
    @19
    simp3
    breqtrrd
    3exp
    rexlimd
    imp
    adantll
    syldan
    ralrimiva
    exp31
    imp
    reximdva
    mpd
    @5
    @9
    vw
    vy
    cr
    @0
    @7
    wceq
    @2
    @8
    vz
    @4
    @0
    @7
    @1
    cle
    breq1
    ralbidv
    cbvrexv
    sylib
end
