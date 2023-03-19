include "wtru.mm"
include "cr.mm"
include "wreu.mm"
include "crio.mm"
include "cneg.mm"
include "wceq.mm"
include "tru.mm"
include "cv.mm"
include "nfriota1.mm"
include "nfneg.mm"
include "wcel.mm"
include "renegcl.mm"
include "adantl.mm"
include "wa.mm"
include "simpr.mm"
include "renegcld.mm"
include "negeq.mm"
include "cc.mm"
include "wb.mm"
include "recn.mm"
include "negcon2.mm"
include "syl2an.mm"
include "reuhyp.mm"
include "riotaxfrd.mm"
include "mpan.mm"

theorem riotaneg
  let wph: wff ph
  let wps: wff ps
  let vx: setvar x
  let vy: setvar y
  assume riotaneg.1: |- ( x = -u y -> ( ph <-> ps ) )

  disjoint x y
  disjoint ph y
  disjoint ps x
  assert |- ( E! x e. RR ph -> ( iota_ x e. RR ph ) = -u ( iota_ y e. RR ps ) )

  proof
    wtru
    wph
    vx
    cr
    wreu
    wph
    vx
    cr
    crio
    wps
    vy
    cr
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
    cr
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
    cr
    nfriota1
    nfneg
    @2
    cr
    wcel
    #
    @3
    cr
    wcel
    wtru
    @2
    renegcl
    adantl
    wtru
    @0
    cr
    wcel
    #
    wa
    @0
    wtru
    @5
    simpr
    renegcld
    riotaneg.1
    @2
    @0
    negeq
    vx
    cv
    #
    cr
    wcel
    #
    @6
    @3
    wceq
    #
    vy
    cr
    wreu
    wtru
    vx
    vy
    @3
    @6
    cneg
    #
    cr
    @6
    renegcl
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
    recn
    @2
    recn
    @6
    @2
    negcon2
    syl2an
    reuhyp
    adantl
    riotaxfrd
    mpan
end
