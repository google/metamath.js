include "wcel.mm"
include "wi.mm"
include "wsbc.mm"
include "nfcv.mm"
include "nfv.mm"
include "nfsbc1v.mm"
include "nfim.mm"
include "cv.mm"
include "wceq.mm"
include "sbceq1a.mm"
include "imbi2d.mm"
include "wb.mm"
include "sbc2iegf.mm"
include "syl2anc.mm"
include "sylan9bb.mm"
include "pm5.74da.mm"
include "vtocl2gf.mm"
include "pm2.43i.mm"

theorem vtocl2d
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let vx: setvar x
  let vy: setvar y
  let cA: class A
  let cB: class B
  let cV: class V
  let cW: class W
  assume vtocl2d.a: |- ( ph -> A e. V )
  assume vtocl2d.b: |- ( ph -> B e. W )
  assume vtocl2d.1: |- ( ( x = A /\ y = B ) -> ( ps <-> ch ) )
  assume vtocl2d.3: |- ( ph -> ps )

  disjoint A x
  disjoint A y
  disjoint x y
  disjoint B x
  disjoint B y
  disjoint V x
  disjoint W x
  disjoint W y
  disjoint ch x
  disjoint ch y
  disjoint ph x
  disjoint ph y
  assert |- ( ph -> ch )

  proof
    wph
    wch
    wph
    cB
    cW
    wcel
    #
    cA
    cV
    wcel
    #
    wph
    wch
    wi
    #
    vtocl2d.b
    vtocl2d.a
    wph
    wps
    wi
    wph
    wps
    vy
    cB
    wsbc
    #
    wi
    @2
    vy
    vx
    cB
    cA
    cW
    cV
    vy
    cB
    nfcv
    vx
    cB
    nfcv
    vx
    cA
    nfcv
    wph
    @3
    vy
    wph
    vy
    nfv
    wps
    vy
    cB
    nfsbc1v
    nfim
    @2
    vx
    nfv
    vy
    cv
    cB
    wceq
    wps
    @3
    wph
    wps
    vy
    cB
    sbceq1a
    imbi2d
    vx
    cv
    cA
    wceq
    #
    wph
    @3
    wch
    @4
    @3
    @3
    vx
    cA
    wsbc
    #
    wph
    wch
    @3
    vx
    cA
    sbceq1a
    wph
    @1
    @0
    @5
    wch
    wb
    vtocl2d.a
    vtocl2d.b
    wps
    wch
    vx
    vy
    cA
    cB
    cV
    cW
    wch
    vx
    nfv
    wch
    vy
    nfv
    @0
    vx
    nfv
    vtocl2d.1
    sbc2iegf
    syl2anc
    sylan9bb
    pm5.74da
    vtocl2d.3
    vtocl2gf
    syl2anc
    pm2.43i
end
