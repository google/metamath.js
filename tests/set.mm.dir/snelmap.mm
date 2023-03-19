include "cv.mm"
include "wcel.mm"
include "wex.mm"
include "c0.mm"
include "wne.mm"
include "n0.mm"
include "sylib.mm"
include "wa.mm"
include "csn.mm"
include "cxp.mm"
include "cfv.mm"
include "wceq.mm"
include "vex.mm"
include "fvconst2.mm"
include "eqcomd.mm"
include "adantl.mm"
include "wf.mm"
include "cmap.mm"
include "co.mm"
include "wb.mm"
include "elmapg.mm"
include "syl2anc.mm"
include "mpbid.mm"
include "adantr.mm"
include "simpr.mm"
include "ffvelrnd.mm"
include "eqeltrd.mm"
include "ex.mm"
include "exlimdv.mm"
include "mpd.mm"

theorem snelmap
  let wph: wff ph
  let vx: setvar x
  let cA: class A
  let cB: class B
  let cV: class V
  let cW: class W
  let vy: setvar y
  assume snelmap.a: |- ( ph -> A e. V )
  assume snelmap.b: |- ( ph -> B e. W )
  assume snelmap.n: |- ( ph -> A =/= (/) )
  assume snelmap.e: |- ( ph -> ( A X. { x } ) e. ( B ^m A ) )


  assert |- ( ph -> x e. B )

  proof
    wph
    vy
    cv
    #
    cA
    wcel
    #
    vy
    wex
    #
    vx
    cv
    #
    cB
    wcel
    #
    wph
    cA
    c0
    wne
    @2
    snelmap.n
    vy
    cA
    n0
    sylib
    wph
    @1
    @4
    vy
    wph
    @1
    @4
    wph
    @1
    wa
    #
    @3
    @0
    cA
    @3
    csn
    cxp
    #
    cfv
    #
    cB
    @1
    @3
    @7
    wceq
    wph
    @1
    @7
    @3
    cA
    @3
    @0
    vx
    vex
    fvconst2
    eqcomd
    adantl
    @5
    cA
    cB
    @0
    @6
    wph
    cA
    cB
    @6
    wf
    #
    @1
    wph
    @6
    cB
    cA
    cmap
    co
    wcel
    #
    @8
    snelmap.e
    wph
    cB
    cW
    wcel
    cA
    cV
    wcel
    @9
    @8
    wb
    snelmap.b
    snelmap.a
    cB
    cA
    @6
    cW
    cV
    elmapg
    syl2anc
    mpbid
    adantr
    wph
    @1
    simpr
    ffvelrnd
    eqeltrd
    ex
    exlimdv
    mpd
end
