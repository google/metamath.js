include "wcel.mm"
include "wa.mm"
include "wsbc.mm"
include "simpl.mm"
include "cv.mm"
include "wceq.mm"
include "wb.mm"
include "adantll.mm"
include "nfv.mm"
include "wnf.mm"
include "a1i.mm"
include "sbciedf.mm"
include "nfan.mm"

theorem sbc2iegf
  let wph: wff ph
  let wps: wff ps
  let vx: setvar x
  let vy: setvar y
  let cA: class A
  let cB: class B
  let cV: class V
  let cW: class W
  assume sbc2iegf.1: |- F/ x ps
  assume sbc2iegf.2: |- F/ y ps
  assume sbc2iegf.3: |- F/ x B e. W
  assume sbc2iegf.4: |- ( ( x = A /\ y = B ) -> ( ph <-> ps ) )

  disjoint x y
  disjoint A x
  disjoint A y
  disjoint B y
  disjoint V x
  disjoint W y
  assert |- ( ( A e. V /\ B e. W ) -> ( [. A / x ]. [. B / y ]. ph <-> ps ) )

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
    wph
    vy
    cB
    wsbc
    #
    wps
    vx
    cA
    cV
    @0
    @1
    simpl
    @1
    vx
    cv
    cA
    wceq
    #
    @3
    wps
    wb
    @0
    @1
    @4
    wa
    #
    wph
    wps
    vy
    cB
    cW
    @1
    @4
    simpl
    @4
    vy
    cv
    cB
    wceq
    wph
    wps
    wb
    @1
    sbc2iegf.4
    adantll
    @5
    vy
    nfv
    wps
    vy
    wnf
    @5
    sbc2iegf.2
    a1i
    sbciedf
    adantll
    @0
    @1
    vx
    @0
    vx
    nfv
    sbc2iegf.3
    nfan
    wps
    vx
    wnf
    @2
    sbc2iegf.1
    a1i
    sbciedf
end
