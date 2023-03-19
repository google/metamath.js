include "cxdiv.mm"
include "co.mm"
include "cv.mm"
include "cxmu.mm"
include "wceq.mm"
include "cxr.mm"
include "crio.mm"
include "wcel.mm"
include "cr.mm"
include "cc0.mm"
include "wne.mm"
include "xdivval.mm"
include "syl3anc.mm"
include "wreu.mm"
include "xreceu.mm"
include "riotacl.mm"
include "syl.mm"
include "eqeltrd.mm"

theorem xdivcld
  let wph: wff ph
  let cA: class A
  let cB: class B
  let vx: setvar x
  assume xdivcld.1: |- ( ph -> A e. RR* )
  assume xdivcld.2: |- ( ph -> B e. RR )
  assume xdivcld.3: |- ( ph -> B =/= 0 )


  assert |- ( ph -> ( A /e B ) e. RR* )

  proof
    wph
    cA
    cB
    cxdiv
    co
    #
    cB
    vx
    cv
    cxmu
    co
    cA
    wceq
    #
    vx
    cxr
    crio
    #
    cxr
    wph
    cA
    cxr
    wcel
    #
    cB
    cr
    wcel
    #
    cB
    cc0
    wne
    #
    @0
    @2
    wceq
    xdivcld.1
    xdivcld.2
    xdivcld.3
    vx
    cA
    cB
    xdivval
    syl3anc
    wph
    @1
    vx
    cxr
    wreu
    #
    @2
    cxr
    wcel
    wph
    @3
    @4
    @5
    @6
    xdivcld.1
    xdivcld.2
    xdivcld.3
    vx
    cA
    cB
    xreceu
    syl3anc
    @1
    vx
    cxr
    riotacl
    syl
    eqeltrd
end
