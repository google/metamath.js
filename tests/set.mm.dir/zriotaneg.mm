include "wtru.mm"
include "cz.mm"
include "wreu.mm"
include "crio.mm"
include "cneg.mm"
include "wceq.mm"
include "tru.mm"
include "cv.mm"
include "nfriota1.mm"
include "nfneg.mm"
include "wcel.mm"
include "znegcl.mm"
include "adantl.mm"
include "wa.mm"
include "simpr.mm"
include "znegcld.mm"
include "negeq.mm"
include "cc.mm"
include "wb.mm"
include "zcn.mm"
include "negcon2.mm"
include "syl2an.mm"
include "reuhyp.mm"
include "riotaxfrd.mm"
include "mpan.mm"

theorem zriotaneg
  let wph: wff ph
  let wps: wff ps
  let vx: setvar x
  let vy: setvar y
  assume zriotaneg.1: |- ( x = -u y -> ( ph <-> ps ) )

  disjoint x y
  disjoint ph y
  disjoint ps x
  assert |- ( E! x e. ZZ ph -> ( iota_ x e. ZZ ph ) = -u ( iota_ y e. ZZ ps ) )

  proof
    wtru
    wph
    vx
    cz
    wreu
    wph
    vx
    cz
    crio
    wps
    vy
    cz
    crio
    #
    cneg
    #
    wceq
    tru
    wtru
    wph
    wps
    vx
    vy
    cz
    vy
    cv
    #
    cneg
    #
    @1
    vy
    @0
    wps
    vy
    cz
    nfriota1
    nfneg
    @2
    cz
    wcel
    #
    @3
    cz
    wcel
    wtru
    @2
    znegcl
    adantl
    wtru
    @0
    cz
    wcel
    #
    wa
    @0
    wtru
    @5
    simpr
    znegcld
    zriotaneg.1
    @2
    @0
    negeq
    vx
    cv
    #
    cz
    wcel
    #
    @6
    @3
    wceq
    #
    vy
    cz
    wreu
    wtru
    vx
    vy
    @3
    @6
    cneg
    #
    cz
    @6
    znegcl
    @7
    @6
    cc
    wcel
    @2
    cc
    wcel
    @8
    @2
    @9
    wceq
    wb
    @4
    @6
    zcn
    @2
    zcn
    @6
    @2
    negcon2
    syl2an
    reuhyp
    adantl
    riotaxfrd
    mpan
end
