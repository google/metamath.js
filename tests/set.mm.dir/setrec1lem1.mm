include "wcel.mm"
include "cv.mm"
include "wss.mm"
include "cfv.mm"
include "wi.mm"
include "wal.mm"
include "wb.mm"
include "wceq.mm"
include "sseq2.mm"
include "imbi1d.mm"
include "albidv.mm"
include "sseq1.mm"
include "imbi12d.mm"
include "elab2g.mm"
include "syl.mm"

theorem setrec1lem1
  let wph: wff ph
  let vy: setvar y
  let vz: setvar z
  let vw: setvar w
  let cF: class F
  let cV: class V
  let cX: class X
  let cY: class Y
  let vk: setvar k
  let vx: setvar x
  assume setrec1lem1.1: |- Y = { y | A. z ( A. w ( w C_ y -> ( w C_ z -> ( F ` w ) C_ z ) ) -> y C_ z ) }
  assume setrec1lem1.2: |- ( ph -> X e. V )

  disjoint F y
  disjoint X w
  disjoint X y
  disjoint w y
  disjoint X z
  disjoint y z
  disjoint k x
  assert |- ( ph -> ( X e. Y <-> A. z ( A. w ( w C_ X -> ( w C_ z -> ( F ` w ) C_ z ) ) -> X C_ z ) ) )

  proof
    wph
    cX
    cV
    wcel
    cX
    cY
    wcel
    vw
    cv
    #
    cX
    wss
    #
    @0
    vz
    cv
    #
    wss
    @0
    cF
    cfv
    @2
    wss
    wi
    #
    wi
    #
    vw
    wal
    #
    cX
    @2
    wss
    #
    wi
    #
    vz
    wal
    #
    wb
    setrec1lem1.2
    @0
    vy
    cv
    #
    wss
    #
    @3
    wi
    #
    vw
    wal
    #
    @9
    @2
    wss
    #
    wi
    #
    vz
    wal
    @8
    vy
    cX
    cY
    cV
    @9
    cX
    wceq
    #
    @14
    @7
    vz
    @15
    @12
    @5
    @13
    @6
    @15
    @11
    @4
    vw
    @15
    @10
    @1
    @3
    @9
    cX
    @0
    sseq2
    imbi1d
    albidv
    @9
    cX
    @2
    sseq1
    imbi12d
    albidv
    setrec1lem1.1
    elab2g
    syl
end
