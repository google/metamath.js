include "chom.mm"
include "cfv.mm"
include "cxp.mm"
include "wfn.mm"
include "chomf.mm"
include "wceq.mm"
include "ringcbas.mm"
include "eqid.mm"
include "ringchomfval.mm"
include "rhmresfn.mm"
include "fnhomeqhomf.mm"
include "syl.mm"

theorem ringchomfeqhom
  let wph: wff ph
  let cB: class B
  let cC: class C
  let cU: class U
  let cV: class V
  let vk: setvar k
  let vx: setvar x
  assume ringcbas.c: |- C = ( RingCat ` U )
  assume ringcbas.b: |- B = ( Base ` C )
  assume ringcbas.u: |- ( ph -> U e. V )


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
    ringcbas.c
    ringcbas.b
    ringcbas.u
    ringcbas
    wph
    cB
    cC
    cU
    @0
    cV
    ringcbas.c
    ringcbas.b
    ringcbas.u
    @0
    eqid
    #
    ringchomfval
    rhmresfn
    cB
    cC
    @1
    @0
    @1
    eqid
    ringcbas.b
    @2
    fnhomeqhomf
    syl
end
