include "cbs.mm"
include "cfv.mm"
include "cestrc.mm"
include "crngh.mm"
include "crng.mm"
include "cin.mm"
include "cxp.mm"
include "cres.mm"
include "cresc.mm"
include "co.mm"
include "eqidd.mm"
include "rngcval.mm"
include "fveq2d.mm"
include "wceq.mm"
include "a1i.mm"
include "cvv.mm"
include "eqid.mm"
include "fvexd.mm"
include "rnghmresfn.mm"
include "inss1.mm"
include "estrcbas.mm"
include "syl5sseq.mm"
include "rescbas.mm"
include "3eqtr4d.mm"

theorem rngcbas
  let wph: wff ph
  let cB: class B
  let cC: class C
  let cU: class U
  let cV: class V
  let vk: setvar k
  let vx: setvar x
  assume rngcbas.c: |- C = ( RngCat ` U )
  assume rngcbas.b: |- B = ( Base ` C )
  assume rngcbas.u: |- ( ph -> U e. V )


  assert |- ( ph -> B = ( U i^i Rng ) )

  proof
    wph
    cC
    cbs
    cfv
    #
    cU
    cestrc
    cfv
    #
    crngh
    cU
    crng
    cin
    #
    @2
    cxp
    cres
    #
    cresc
    co
    #
    cbs
    cfv
    cB
    @2
    wph
    cC
    @4
    cbs
    wph
    @2
    cC
    cU
    @3
    cV
    rngcbas.c
    rngcbas.u
    wph
    @2
    eqidd
    #
    wph
    @3
    eqidd
    #
    rngcval
    fveq2d
    cB
    @0
    wceq
    wph
    rngcbas.b
    a1i
    wph
    @1
    cbs
    cfv
    #
    @1
    @4
    @2
    @3
    cvv
    @4
    eqid
    @7
    eqid
    wph
    cU
    cestrc
    fvexd
    wph
    @2
    cU
    @3
    @5
    @6
    rnghmresfn
    wph
    cU
    @2
    @7
    cU
    crng
    inss1
    wph
    @1
    cU
    cV
    @1
    eqid
    rngcbas.u
    estrcbas
    syl5sseq
    rescbas
    3eqtr4d
end
