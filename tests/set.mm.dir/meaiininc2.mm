include "cv.mm"
include "cfv.mm"
include "cr.mm"
include "wcel.mm"
include "wrex.mm"
include "ciin.mm"
include "cli.mm"
include "wbr.mm"
include "nfv.mm"
include "w3a.mm"
include "nf3an.mm"
include "cmea.mm"
include "3ad2ant1.mm"
include "cz.mm"
include "cdm.mm"
include "wf.mm"
include "c1.mm"
include "caddc.mm"
include "co.mm"
include "wss.mm"
include "3ad2antl1.mm"
include "cuz.mm"
include "id.mm"
include "syl6eleq.mm"
include "3ad2ant2.mm"
include "simp3.mm"
include "meaiininc.mm"
include "3exp.mm"
include "rexlimd.mm"
include "mpd.mm"

theorem meaiininc2
  let wph: wff ph
  let cS: class S
  let vk: setvar k
  let vn: setvar n
  let cE: class E
  let cM: class M
  let cN: class N
  let cZ: class Z
  let vx: setvar x
  assume meaiininc2.f: |- F/ n ph
  assume meaiininc2.p: |- F/ k ph
  assume meaiininc2.m: |- ( ph -> M e. Meas )
  assume meaiininc2.n: |- ( ph -> N e. ZZ )
  assume meaiininc2.z: |- Z = ( ZZ>= ` N )
  assume meaiininc2.e: |- ( ph -> E : Z --> dom M )
  assume meaiininc2.i: |- ( ( ph /\ n e. Z ) -> ( E ` ( n + 1 ) ) C_ ( E ` n ) )
  assume meaiininc2.k: |- ( ph -> E. k e. Z ( M ` ( E ` k ) ) e. RR )
  assume meaiininc2.s: |- S = ( n e. Z |-> ( M ` ( E ` n ) ) )

  disjoint E k
  disjoint E n
  disjoint k n
  disjoint M k
  disjoint M n
  disjoint S k
  disjoint Z k
  disjoint Z n
  disjoint k x
  assert |- ( ph -> S ~~> ( M ` |^|_ n e. Z ( E ` n ) ) )

  proof
    wph
    vk
    cv
    #
    cE
    cfv
    cM
    cfv
    cr
    wcel
    #
    vk
    cZ
    wrex
    cS
    vn
    cZ
    vn
    cv
    #
    cE
    cfv
    #
    ciin
    cM
    cfv
    cli
    wbr
    #
    meaiininc2.k
    wph
    @1
    @4
    vk
    cZ
    meaiininc2.p
    @4
    vk
    nfv
    wph
    @0
    cZ
    wcel
    #
    @1
    @4
    wph
    @5
    @1
    w3a
    cS
    vn
    cE
    @0
    cM
    cN
    cZ
    wph
    @5
    @1
    vn
    meaiininc2.f
    @5
    vn
    nfv
    @1
    vn
    nfv
    nf3an
    wph
    @5
    cM
    cmea
    wcel
    @1
    meaiininc2.m
    3ad2ant1
    wph
    @5
    cN
    cz
    wcel
    @1
    meaiininc2.n
    3ad2ant1
    meaiininc2.z
    wph
    @5
    cZ
    cM
    cdm
    cE
    wf
    @1
    meaiininc2.e
    3ad2ant1
    wph
    @5
    @2
    cZ
    wcel
    @2
    c1
    caddc
    co
    cE
    cfv
    @3
    wss
    @1
    meaiininc2.i
    3ad2antl1
    @5
    wph
    @0
    cN
    cuz
    cfv
    #
    wcel
    @1
    @5
    @0
    cZ
    @6
    @5
    id
    meaiininc2.z
    syl6eleq
    3ad2ant2
    wph
    @5
    @1
    simp3
    meaiininc2.s
    meaiininc
    3exp
    rexlimd
    mpd
end
