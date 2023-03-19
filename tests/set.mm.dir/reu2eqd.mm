include "wceq.mm"
include "wsb.mm"
include "wa.mm"
include "cv.mm"
include "wi.mm"
include "wral.mm"
include "wrex.mm"
include "wreu.mm"
include "reu2.mm"
include "sylib.mm"
include "simprd.mm"
include "wcel.mm"
include "nfv.mm"
include "nfs1v.mm"
include "nfan.mm"
include "nfim.mm"
include "anbi1d.mm"
include "eqeq1.mm"
include "imbi12d.mm"
include "sbhypf.mm"
include "anbi2d.mm"
include "eqeq2.mm"
include "rspc2.mm"
include "syl2anc.mm"
include "mpd.mm"
include "mp2and.mm"

theorem reu2eqd
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let wth: wff th
  let vx: setvar x
  let cA: class A
  let cB: class B
  let cC: class C
  let vy: setvar y
  assume reu2eqd.1: |- ( x = B -> ( ps <-> ch ) )
  assume reu2eqd.2: |- ( x = C -> ( ps <-> th ) )
  assume reu2eqd.3: |- ( ph -> E! x e. A ps )
  assume reu2eqd.4: |- ( ph -> B e. A )
  assume reu2eqd.5: |- ( ph -> C e. A )
  assume reu2eqd.6: |- ( ph -> ch )
  assume reu2eqd.7: |- ( ph -> th )

  disjoint A x
  disjoint B x
  disjoint C x
  disjoint ch x
  disjoint th x
  disjoint A y
  disjoint x y
  disjoint B y
  disjoint C y
  disjoint ch y
  disjoint ps y
  disjoint th y
  assert |- ( ph -> B = C )

  proof
    wph
    wch
    wth
    cB
    cC
    wceq
    #
    reu2eqd.6
    reu2eqd.7
    wph
    wps
    wps
    vx
    vy
    wsb
    #
    wa
    #
    vx
    cv
    #
    vy
    cv
    #
    wceq
    #
    wi
    #
    vy
    cA
    wral
    vx
    cA
    wral
    #
    wch
    wth
    wa
    #
    @0
    wi
    #
    wph
    wps
    vx
    cA
    wrex
    #
    @7
    wph
    wps
    vx
    cA
    wreu
    @10
    @7
    wa
    reu2eqd.3
    wps
    vx
    vy
    cA
    reu2
    sylib
    simprd
    wph
    cB
    cA
    wcel
    cC
    cA
    wcel
    @7
    @9
    wi
    reu2eqd.4
    reu2eqd.5
    @6
    @9
    wch
    @1
    wa
    #
    cB
    @4
    wceq
    #
    wi
    vx
    vy
    cB
    cC
    cA
    cA
    @11
    @12
    vx
    wch
    @1
    vx
    wch
    vx
    nfv
    wps
    vx
    vy
    nfs1v
    nfan
    @12
    vx
    nfv
    nfim
    @9
    vy
    nfv
    @3
    cB
    wceq
    #
    @2
    @11
    @5
    @12
    @13
    wps
    wch
    @1
    reu2eqd.1
    anbi1d
    @3
    cB
    @4
    eqeq1
    imbi12d
    @4
    cC
    wceq
    #
    @11
    @8
    @12
    @0
    @14
    @1
    wth
    wch
    wps
    wth
    vx
    vy
    cC
    wth
    vx
    nfv
    reu2eqd.2
    sbhypf
    anbi2d
    @4
    cC
    cB
    eqeq2
    imbi12d
    rspc2
    syl2anc
    mpd
    mp2and
end
