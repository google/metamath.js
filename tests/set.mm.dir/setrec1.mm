include "cfv.mm"
include "cv.mm"
include "wss.mm"
include "wi.mm"
include "wal.mm"
include "cab.mm"
include "cuni.mm"
include "wcel.mm"
include "wa.mm"
include "eqid.mm"
include "wex.mm"
include "sseld.mm"
include "imp.mm"
include "csetrecs.mm"
include "df-setrecs.mm"
include "eqtri.mm"
include "syl6eleq.mm"
include "eluni.mm"
include "sylib.mm"
include "ralrimiva.mm"
include "setrec1lem3.mm"
include "cun.mm"
include "nfv.mm"
include "nfaba1.mm"
include "nfel2.mm"
include "nfan.mm"
include "cvv.mm"
include "adantr.mm"
include "simprl.mm"
include "simprr.mm"
include "setrec1lem4.mm"
include "ssun2.mm"
include "jctil.mm"
include "ssuni.mm"
include "syl.mm"
include "exlimddv.mm"
include "syl6sseqr.mm"

theorem setrec1
  let wph: wff ph
  let cA: class A
  let cB: class B
  let cF: class F
  let va: setvar a
  let vw: setvar w
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let vk: setvar k
  assume setrec1.b: |- B = setrecs ( F )
  assume setrec1.v: |- ( ph -> A e. _V )
  assume setrec1.a: |- ( ph -> A C_ B )


  assert |- ( ph -> ( F ` A ) C_ B )

  proof
    wph
    cA
    cF
    cfv
    #
    vw
    cv
    #
    vy
    cv
    #
    wss
    @1
    vz
    cv
    #
    wss
    @1
    cF
    cfv
    @3
    wss
    wi
    wi
    vw
    wal
    @2
    @3
    wss
    wi
    #
    vz
    wal
    vy
    cab
    #
    cuni
    #
    cB
    wph
    cA
    vx
    cv
    #
    wss
    #
    @7
    @5
    wcel
    #
    wa
    #
    @0
    @6
    wss
    #
    vx
    wph
    vx
    vy
    vz
    vw
    cA
    cF
    @5
    va
    @5
    eqid
    #
    setrec1.v
    wph
    va
    cv
    #
    @7
    wcel
    @9
    wa
    vx
    wex
    #
    va
    cA
    wph
    @13
    cA
    wcel
    #
    wa
    #
    @13
    @6
    wcel
    @14
    @16
    @13
    cB
    @6
    wph
    @15
    @13
    cB
    wcel
    wph
    cA
    cB
    @13
    setrec1.a
    sseld
    imp
    cB
    cF
    csetrecs
    @6
    setrec1.b
    vy
    vz
    vw
    cF
    df-setrecs
    eqtri
    #
    syl6eleq
    vx
    @13
    @5
    eluni
    sylib
    ralrimiva
    setrec1lem3
    wph
    @10
    wa
    #
    @0
    @7
    @0
    cun
    #
    wss
    #
    @19
    @5
    wcel
    #
    wa
    @11
    @18
    @21
    @20
    @18
    vy
    vz
    vw
    cA
    cF
    @7
    @5
    wph
    @10
    vz
    wph
    vz
    nfv
    @8
    @9
    vz
    @8
    vz
    nfv
    vz
    @7
    @5
    @4
    vz
    vy
    nfaba1
    nfel2
    nfan
    nfan
    @12
    wph
    cA
    cvv
    wcel
    @10
    setrec1.v
    adantr
    wph
    @8
    @9
    simprl
    wph
    @8
    @9
    simprr
    setrec1lem4
    @0
    @7
    ssun2
    jctil
    @0
    @19
    @5
    ssuni
    syl
    exlimddv
    @17
    syl6sseqr
end
