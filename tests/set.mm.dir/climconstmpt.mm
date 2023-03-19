include "cmpt.mm"
include "csn.mm"
include "cxp.mm"
include "cli.mm"
include "fconstmpt.mm"
include "cc.mm"
include "wcel.mm"
include "cz.mm"
include "wbr.mm"
include "cuz.mm"
include "cfv.mm"
include "eqcomi.mm"
include "ssid.mm"
include "eqsstri.mm"
include "cvv.mm"
include "fvex.mm"
include "eqeltri.mm"
include "climconst2.mm"
include "syl2anc.mm"
include "syl5eqbrr.mm"

theorem climconstmpt
  let wph: wff ph
  let vx: setvar x
  let cA: class A
  let cM: class M
  let cZ: class Z
  assume climconstmpt.m: |- ( ph -> M e. ZZ )
  assume climconstmpt.z: |- Z = ( ZZ>= ` M )
  assume climconstmpt.a: |- ( ph -> A e. CC )

  disjoint A x
  disjoint Z x
  assert |- ( ph -> ( x e. Z |-> A ) ~~> A )

  proof
    wph
    vx
    cZ
    cA
    cmpt
    cZ
    cA
    csn
    cxp
    #
    cA
    cli
    vx
    cZ
    cA
    fconstmpt
    wph
    cA
    cc
    wcel
    cM
    cz
    wcel
    @0
    cA
    cli
    wbr
    climconstmpt.a
    climconstmpt.m
    cA
    cM
    cZ
    cM
    cuz
    cfv
    #
    cZ
    cZ
    cZ
    @1
    climconstmpt.z
    eqcomi
    cZ
    ssid
    eqsstri
    cZ
    @1
    cvv
    climconstmpt.z
    cM
    cuz
    fvex
    eqeltri
    climconst2
    syl2anc
    syl5eqbrr
end
