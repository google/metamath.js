include "crng.mm"
include "cv.mm"
include "crngh.mm"
include "co.mm"
include "cmpt2.mm"
include "cbs.mm"
include "cfv.mm"
include "cxp.mm"
include "cres.mm"
include "wss.mm"
include "wceq.mm"
include "cin.mm"
include "eqid.mm"
include "rngcbasALTV.mm"
include "inss2.mm"
include "syl6eqss.mm"
include "resmpt2.mm"
include "syl2anc.mm"
include "wfn.mm"
include "cplusg.mm"
include "cmulr.mm"
include "wa.mm"
include "wral.mm"
include "cmap.mm"
include "crab.mm"
include "csb.mm"
include "df-rnghomo.mm"
include "ovex.mm"
include "rabex.mm"
include "csbex.mm"
include "fnmpt2i.mm"
include "a1i.mm"
include "fnov.mm"
include "sylib.mm"
include "incom.mm"
include "3eqtr4rd.mm"
include "sqxpeqd.mm"
include "reseq12d.mm"
include "rngchomffvalALTV.mm"

theorem rngchomrnghmresALTV
  let wph: wff ph
  let cB: class B
  let cC: class C
  let cU: class U
  let cF: class F
  let cV: class V
  let vx: setvar x
  let vy: setvar y
  let vr: setvar r
  let vs: setvar s
  let vv: setvar v
  let vw: setvar w
  let vf: setvar f
  let vk: setvar k
  assume rngchomrnghmresALTV.c: |- C = ( RngCatALTV ` U )
  assume rngchomrnghmresALTV.b: |- B = ( Rng i^i U )
  assume rngchomrnghmresALTV.u: |- ( ph -> U e. V )
  assume rngchomrnghmresALTV.f: |- F = ( Homf ` C )


  assert |- ( ph -> F = ( RngHomo |` ( B X. B ) ) )

  proof
    wph
    vx
    vy
    crng
    crng
    vx
    cv
    #
    vy
    cv
    #
    crngh
    co
    #
    cmpt2
    #
    cC
    cbs
    cfv
    #
    @4
    cxp
    #
    cres
    #
    vx
    vy
    @4
    @4
    @2
    cmpt2
    #
    crngh
    cB
    cB
    cxp
    #
    cres
    cF
    wph
    @4
    crng
    wss
    #
    @9
    @6
    @7
    wceq
    wph
    @4
    cU
    crng
    cin
    #
    crng
    wph
    @4
    cC
    cU
    cV
    rngchomrnghmresALTV.c
    @4
    eqid
    #
    rngchomrnghmresALTV.u
    rngcbasALTV
    #
    cU
    crng
    inss2
    syl6eqss
    #
    @13
    vx
    vy
    crng
    crng
    @4
    @4
    @2
    resmpt2
    syl2anc
    wph
    crngh
    @3
    @8
    @5
    wph
    crngh
    crng
    crng
    cxp
    wfn
    #
    crngh
    @3
    wceq
    @14
    wph
    vr
    vs
    crng
    crng
    vv
    vr
    cv
    #
    cbs
    cfv
    #
    vw
    vs
    cv
    #
    cbs
    cfv
    #
    @0
    @1
    @15
    cplusg
    cfv
    co
    vf
    cv
    #
    cfv
    @0
    @19
    cfv
    #
    @1
    @19
    cfv
    #
    @17
    cplusg
    cfv
    co
    wceq
    @0
    @1
    @15
    cmulr
    cfv
    co
    @19
    cfv
    @20
    @21
    @17
    cmulr
    cfv
    co
    wceq
    wa
    vy
    vv
    cv
    #
    wral
    vx
    @22
    wral
    #
    vf
    vw
    cv
    #
    @22
    cmap
    co
    #
    crab
    #
    csb
    #
    csb
    crngh
    vx
    vy
    vw
    vv
    vf
    vs
    vr
    df-rnghomo
    vv
    @16
    @27
    vw
    @18
    @26
    @23
    vf
    @25
    @24
    @22
    cmap
    ovex
    rabex
    csbex
    csbex
    fnmpt2i
    a1i
    vx
    vy
    crng
    crng
    crngh
    fnov
    sylib
    wph
    cB
    @4
    wph
    @10
    crng
    cU
    cin
    #
    @4
    cB
    @10
    @28
    wceq
    wph
    cU
    crng
    incom
    a1i
    @12
    cB
    @28
    wceq
    wph
    rngchomrnghmresALTV.b
    a1i
    3eqtr4rd
    sqxpeqd
    reseq12d
    wph
    vx
    vy
    @4
    cC
    cU
    cF
    cV
    rngchomrnghmresALTV.c
    @11
    rngchomrnghmresALTV.u
    rngchomrnghmresALTV.f
    rngchomffvalALTV
    3eqtr4rd
end
