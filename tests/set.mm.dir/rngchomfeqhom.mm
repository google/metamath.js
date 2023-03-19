include "chom.mm"
include "cfv.mm"
include "cxp.mm"
include "wfn.mm"
include "chomf.mm"
include "wceq.mm"
include "rngcbas.mm"
include "eqid.mm"
include "rngchomfval.mm"
include "rnghmresfn.mm"
include "fnhomeqhomf.mm"
include "syl.mm"

theorem rngchomfeqhom
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


  assert |- ( ph -> ( Homf ` C ) = ( Hom ` C ) )

  proof
    wph
    cC
    chom
    cfv
    #
    cB
    cB
    cxp
    wfn
    cC
    chomf
    cfv
    #
    @0
    wceq
    wph
    cB
    cU
    @0
    wph
    cB
    cC
    cU
    cV
    rngcbas.c
    rngcbas.b
    rngcbas.u
    rngcbas
    wph
    cB
    cC
    cU
    @0
    cV
    rngcbas.c
    rngcbas.b
    rngcbas.u
    @0
    eqid
    #
    rngchomfval
    rnghmresfn
    cB
    cC
    @1
    @0
    @1
    eqid
    rngcbas.b
    @2
    fnhomeqhomf
    syl
end
