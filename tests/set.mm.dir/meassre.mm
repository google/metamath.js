include "cc0.mm"
include "cpnf.mm"
include "cico.mm"
include "co.mm"
include "cr.mm"
include "cfv.mm"
include "rge0ssre.mm"
include "cxr.mm"
include "wcel.mm"
include "0xr.mm"
include "a1i.mm"
include "pnfxr.mm"
include "cdm.mm"
include "eqid.mm"
include "meaxrcl.mm"
include "meage0.mm"
include "rexrd.mm"
include "meassle.mm"
include "ltpnfd.mm"
include "xrlelttrd.mm"
include "elicod.mm"
include "sseldi.mm"

theorem meassre
  let wph: wff ph
  let cA: class A
  let cB: class B
  let cM: class M
  let vk: setvar k
  let vx: setvar x
  assume meassre.m: |- ( ph -> M e. Meas )
  assume meassre.a: |- ( ph -> A e. dom M )
  assume meassre.r: |- ( ph -> ( M ` A ) e. RR )
  assume meassre.s: |- ( ph -> B C_ A )
  assume meassre.b: |- ( ph -> B e. dom M )


  assert |- ( ph -> ( M ` B ) e. RR )

  proof
    wph
    cc0
    cpnf
    cico
    co
    cr
    cB
    cM
    cfv
    #
    rge0ssre
    wph
    cc0
    cpnf
    @0
    cc0
    cxr
    wcel
    wph
    0xr
    a1i
    cpnf
    cxr
    wcel
    wph
    pnfxr
    a1i
    #
    wph
    cB
    cM
    cdm
    #
    cM
    meassre.m
    @2
    eqid
    #
    meassre.b
    meaxrcl
    #
    wph
    cB
    cM
    meassre.m
    meassre.b
    meage0
    wph
    @0
    cA
    cM
    cfv
    #
    cpnf
    @4
    wph
    @5
    meassre.r
    rexrd
    @1
    wph
    cB
    cA
    @2
    cM
    meassre.m
    @3
    meassre.b
    meassre.a
    meassre.s
    meassle
    wph
    @5
    meassre.r
    ltpnfd
    xrlelttrd
    elicod
    sseldi
end
