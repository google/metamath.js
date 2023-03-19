include "cxp.mm"
include "wfn.mm"
include "crngh.mm"
include "cres.mm"
include "crng.mm"
include "wss.mm"
include "rnghmfn.mm"
include "cin.mm"
include "inss2.mm"
include "syl6eqss.mm"
include "xpss12.mm"
include "syl2anc.mm"
include "fnssres.mm"
include "sylancr.mm"
include "fneq1d.mm"
include "mpbird.mm"

theorem rnghmresfn
  let wph: wff ph
  let cB: class B
  let cU: class U
  let cH: class H
  let vk: setvar k
  let vx: setvar x
  assume rnghmresfn.b: |- ( ph -> B = ( U i^i Rng ) )
  assume rnghmresfn.h: |- ( ph -> H = ( RngHomo |` ( B X. B ) ) )


  assert |- ( ph -> H Fn ( B X. B ) )

  proof
    wph
    cH
    cB
    cB
    cxp
    #
    wfn
    crngh
    @0
    cres
    #
    @0
    wfn
    #
    wph
    crngh
    crng
    crng
    cxp
    #
    wfn
    @0
    @3
    wss
    #
    @2
    rnghmfn
    wph
    cB
    crng
    wss
    #
    @5
    @4
    wph
    cB
    cU
    crng
    cin
    crng
    rnghmresfn.b
    cU
    crng
    inss2
    syl6eqss
    #
    @6
    cB
    crng
    cB
    crng
    xpss12
    syl2anc
    @3
    @0
    crngh
    fnssres
    sylancr
    wph
    @0
    cH
    @1
    rnghmresfn.h
    fneq1d
    mpbird
end
