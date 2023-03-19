include "cv.mm"
include "cle.mm"
include "wbr.mm"
include "wral.mm"
include "cr.mm"
include "wrex.mm"
include "cmpt.mm"
include "crn.mm"
include "wcel.mm"
include "wa.mm"
include "wceq.mm"
include "cvv.mm"
include "wb.mm"
include "vex.mm"
include "eqid.mm"
include "elrnmpt.mm"
include "ax-mp.mm"
include "biimpi.mm"
include "adantl.mm"
include "nfv.mm"
include "nfan.mm"
include "nfra1.mm"
include "wi.mm"
include "w3a.mm"
include "rspa.mm"
include "3adant3.mm"
include "simp3.mm"
include "simpr.mm"
include "simpl.mm"
include "eqbrtrd.mm"
include "syl2anc.mm"
include "3exp.mm"
include "rexlimd.mm"
include "imp.mm"
include "syldan.mm"
include "ralrimiva.mm"
include "ex.mm"
include "reximdva.mm"
include "mpd.mm"

theorem rnmptbddlem
  let wph: wff ph
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let cA: class A
  let cB: class B
  assume rnmptbddlem.x: |- F/ x ph
  assume rnmptbddlem.b: |- ( ph -> E. y e. RR A. x e. A B <_ y )

  disjoint A z
  disjoint B z
  disjoint ph y
  disjoint ph z
  disjoint y z
  disjoint x y
  disjoint x z
  assert |- ( ph -> E. y e. RR A. z e. ran ( x e. A |-> B ) z <_ y )

  proof
    wph
    cB
    vy
    cv
    #
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
    vz
    cv
    #
    @0
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
    vy
    cr
    wrex
    rnmptbddlem.b
    wph
    @2
    @7
    vy
    cr
    wph
    @0
    cr
    wcel
    #
    wa
    #
    @2
    @7
    @9
    @2
    wa
    #
    @4
    vz
    @6
    @10
    @3
    @6
    wcel
    #
    @3
    cB
    wceq
    #
    vx
    cA
    wrex
    #
    @4
    @11
    @13
    @10
    @11
    @13
    @3
    cvv
    wcel
    @11
    @13
    wb
    vz
    vex
    vx
    cA
    cB
    @3
    @5
    cvv
    @5
    eqid
    elrnmpt
    ax-mp
    biimpi
    adantl
    @10
    @13
    @4
    @10
    @12
    @4
    vx
    cA
    @9
    @2
    vx
    wph
    @8
    vx
    rnmptbddlem.x
    @8
    vx
    nfv
    nfan
    @1
    vx
    cA
    nfra1
    nfan
    @4
    vx
    nfv
    @2
    vx
    cv
    cA
    wcel
    #
    @12
    @4
    wi
    wi
    @9
    @2
    @14
    @12
    @4
    @2
    @14
    @12
    w3a
    @1
    @12
    @4
    @2
    @14
    @1
    @12
    @1
    vx
    cA
    rspa
    3adant3
    @2
    @14
    @12
    simp3
    @1
    @12
    wa
    @3
    cB
    @0
    cle
    @1
    @12
    simpr
    @1
    @12
    simpl
    eqbrtrd
    syl2anc
    3exp
    adantl
    rexlimd
    imp
    syldan
    ralrimiva
    ex
    reximdva
    mpd
end
