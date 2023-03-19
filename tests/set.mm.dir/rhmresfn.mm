include "cxp.mm"
include "wfn.mm"
include "crh.mm"
include "cres.mm"
include "crg.mm"
include "wss.mm"
include "rhmfn.mm"
include "cin.mm"
include "inss2.mm"
include "syl6eqss.mm"
include "xpss12.mm"
include "syl2anc.mm"
include "fnssres.mm"
include "sylancr.mm"
include "fneq1d.mm"
include "mpbird.mm"

theorem rhmresfn
  let wph: wff ph
  let cB: class B
  let cU: class U
  let cH: class H
  let vk: setvar k
  let vx: setvar x
  assume rhmresfn.b: |- ( ph -> B = ( U i^i Ring ) )
  assume rhmresfn.h: |- ( ph -> H = ( RingHom |` ( B X. B ) ) )


  assert |- ( ph -> H Fn ( B X. B ) )

  proof
    wph
    cH
    cB
    cB
    cxp
    #
    wfn
    crh
    @0
    cres
    #
    @0
    wfn
    #
    wph
    crh
    crg
    crg
    cxp
    #
    wfn
    @0
    @3
    wss
    #
    @2
    rhmfn
    wph
    cB
    crg
    wss
    #
    @5
    @4
    wph
    cB
    cU
    crg
    cin
    crg
    rhmresfn.b
    cU
    crg
    inss2
    syl6eqss
    #
    @6
    cB
    crg
    cB
    crg
    xpss12
    syl2anc
    @3
    @0
    crh
    fnssres
    sylancr
    wph
    @0
    cH
    @1
    rhmresfn.h
    fneq1d
    mpbird
end
