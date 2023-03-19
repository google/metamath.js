include "wreu.mm"
include "weq.mm"
include "wi.mm"
include "wral.mm"
include "wa.mm"
include "wrex.mm"
include "nfv.mm"
include "cbvreu.mm"
include "reu8.mm"
include "nfcv.mm"
include "nfim.mm"
include "nfral.mm"
include "nfan.mm"
include "wb.mm"
include "bicomd.mm"
include "equcoms.mm"
include "equequ1.mm"
include "imbi2d.mm"
include "ralbidv.mm"
include "anbi12d.mm"
include "cbvrex.mm"
include "3bitri.mm"

theorem reu8nf
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let vx: setvar x
  let vy: setvar y
  let vw: setvar w
  let cA: class A
  assume reu8nf.1: |- F/ x ps
  assume reu8nf.2: |- F/ x ch
  assume reu8nf.3: |- ( x = w -> ( ph <-> ch ) )
  assume reu8nf.4: |- ( w = y -> ( ch <-> ps ) )

  disjoint w x
  disjoint w y
  disjoint A w
  disjoint x y
  disjoint A x
  disjoint A y
  disjoint ph w
  disjoint ps w
  disjoint ch y
  assert |- ( E! x e. A ph <-> E. x e. A ( ph /\ A. y e. A ( ps -> x = y ) ) )

  proof
    wph
    vx
    cA
    wreu
    wch
    vw
    cA
    wreu
    wch
    wps
    vw
    vy
    weq
    #
    wi
    #
    vy
    cA
    wral
    #
    wa
    #
    vw
    cA
    wrex
    wph
    wps
    vx
    vy
    weq
    #
    wi
    #
    vy
    cA
    wral
    #
    wa
    #
    vx
    cA
    wrex
    wph
    wch
    vx
    vw
    cA
    wph
    vw
    nfv
    reu8nf.2
    reu8nf.3
    cbvreu
    wch
    wps
    vw
    vy
    cA
    reu8nf.4
    reu8
    @3
    @7
    vw
    vx
    cA
    wch
    @2
    vx
    reu8nf.2
    @1
    vx
    vy
    cA
    vx
    cA
    nfcv
    wps
    @0
    vx
    reu8nf.1
    @0
    vx
    nfv
    nfim
    nfral
    nfan
    @7
    vw
    nfv
    vw
    vx
    weq
    #
    wch
    wph
    @2
    @6
    wch
    wph
    wb
    vx
    vw
    vx
    vw
    weq
    wph
    wch
    reu8nf.3
    bicomd
    equcoms
    @8
    @1
    @5
    vy
    cA
    @8
    @0
    @4
    wps
    vw
    vx
    vy
    equequ1
    imbi2d
    ralbidv
    anbi12d
    cbvrex
    3bitri
end
