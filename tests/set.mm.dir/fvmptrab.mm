include "wcel.mm"
include "cfv.mm"
include "crab.mm"
include "wceq.mm"
include "cvv.mm"
include "cmpt.mm"
include "a1i.mm"
include "cv.mm"
include "rabeqbidv.mm"
include "adantl.mm"
include "id.mm"
include "eqid.mm"
include "rabexd.mm"
include "fvmptd.mm"
include "wn.mm"
include "c0.mm"
include "fvmptndm.mm"
include "wnel.mm"
include "df-nel.mm"
include "rabeq.mm"
include "rab0.mm"
include "syl6req.mm"
include "syl.mm"
include "sylbir.mm"
include "eqtrd.mm"
include "pm2.61i.mm"

theorem fvmptrab
  let wph: wff ph
  let wps: wff ps
  let vx: setvar x
  let vy: setvar y
  let cF: class F
  let cM: class M
  let cN: class N
  let cV: class V
  let cX: class X
  let vk: setvar k
  assume fvmptrab.f: |- F = ( x e. V |-> { y e. M | ph } )
  assume fvmptrab.r: |- ( x = X -> ( ph <-> ps ) )
  assume fvmptrab.s: |- ( x = X -> M = N )
  assume fvmptrab.v: |- ( X e. V -> N e. _V )
  assume fvmptrab.n: |- ( X e/ V -> N = (/) )

  disjoint M y
  disjoint N x
  disjoint N y
  disjoint x y
  disjoint X x
  disjoint X y
  disjoint V x
  disjoint ps x
  disjoint k x
  assert |- ( F ` X ) = { y e. N | ps }

  proof
    cX
    cV
    wcel
    #
    cX
    cF
    cfv
    #
    wps
    vy
    cN
    crab
    #
    wceq
    @0
    vx
    cX
    wph
    vy
    cM
    crab
    #
    @2
    cV
    cF
    cvv
    cF
    vx
    cV
    @3
    cmpt
    wceq
    @0
    fvmptrab.f
    a1i
    vx
    cv
    cX
    wceq
    #
    @3
    @2
    wceq
    @0
    @4
    wph
    wps
    vy
    cM
    cN
    fvmptrab.s
    fvmptrab.r
    rabeqbidv
    adantl
    @0
    id
    @0
    wps
    vy
    cN
    @2
    cvv
    @2
    eqid
    fvmptrab.v
    rabexd
    fvmptd
    @0
    wn
    #
    @1
    c0
    @2
    vx
    cV
    @3
    cF
    cX
    fvmptrab.f
    fvmptndm
    @5
    cX
    cV
    wnel
    #
    c0
    @2
    wceq
    #
    cX
    cV
    df-nel
    @6
    cN
    c0
    wceq
    #
    @7
    fvmptrab.n
    @8
    @2
    wps
    vy
    c0
    crab
    c0
    wps
    vy
    cN
    c0
    rabeq
    wps
    vy
    rab0
    syl6req
    syl
    sylbir
    eqtrd
    pm2.61i
end
