include "cco.mm"
include "cfv.mm"
include "cestrc.mm"
include "chom.mm"
include "cresc.mm"
include "co.mm"
include "cbs.mm"
include "eqid.mm"
include "ringcbas.mm"
include "ringchomfval.mm"
include "ringcval.mm"
include "fveq2d.mm"
include "wceq.mm"
include "a1i.mm"
include "cvv.mm"
include "fvexd.mm"
include "rhmresfn.mm"
include "crg.mm"
include "cin.mm"
include "wss.mm"
include "inss1.mm"
include "estrcbas.mm"
include "eqcomd.mm"
include "3sstr4d.mm"
include "rescco.mm"
include "3eqtr4d.mm"

theorem ringccofval
  let wph: wff ph
  let cC: class C
  let c.x: class .x.
  let cU: class U
  let cV: class V
  let vk: setvar k
  let vx: setvar x
  assume ringcco.c: |- C = ( RingCat ` U )
  assume ringcco.u: |- ( ph -> U e. V )
  assume ringcco.o: |- .x. = ( comp ` C )


  assert |- ( ph -> .x. = ( comp ` ( ExtStrCat ` U ) ) )

  proof
    wph
    cC
    cco
    cfv
    #
    cU
    cestrc
    cfv
    #
    cC
    chom
    cfv
    #
    cresc
    co
    #
    cco
    cfv
    c.x
    @1
    cco
    cfv
    #
    wph
    cC
    @3
    cco
    wph
    cC
    cbs
    cfv
    #
    cC
    cU
    @2
    cV
    ringcco.c
    ringcco.u
    wph
    @5
    cC
    cU
    cV
    ringcco.c
    @5
    eqid
    #
    ringcco.u
    ringcbas
    #
    wph
    @5
    cC
    cU
    @2
    cV
    ringcco.c
    @6
    ringcco.u
    @2
    eqid
    ringchomfval
    #
    ringcval
    fveq2d
    c.x
    @0
    wceq
    wph
    ringcco.o
    a1i
    wph
    @1
    cbs
    cfv
    #
    @1
    @3
    @5
    @4
    @2
    cvv
    @3
    eqid
    @9
    eqid
    wph
    cU
    cestrc
    fvexd
    wph
    @5
    cU
    @2
    @7
    @8
    rhmresfn
    wph
    cU
    crg
    cin
    #
    cU
    @5
    @9
    @10
    cU
    wss
    wph
    cU
    crg
    inss1
    a1i
    @7
    wph
    cU
    @9
    wph
    @1
    cU
    cV
    @1
    eqid
    ringcco.u
    estrcbas
    eqcomd
    3sstr4d
    @4
    eqid
    rescco
    3eqtr4d
end
