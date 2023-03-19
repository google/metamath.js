include "cestrc.mm"
include "cfv.mm"
include "crh.mm"
include "cxp.mm"
include "cres.mm"
include "cresc.mm"
include "co.mm"
include "chom.mm"
include "ringcbas.mm"
include "eqidd.mm"
include "ringcval.mm"
include "fveq2d.mm"
include "syl5eq.mm"
include "cbs.mm"
include "cvv.mm"
include "eqid.mm"
include "fvexd.mm"
include "rhmresfn.mm"
include "crg.mm"
include "cin.mm"
include "wss.mm"
include "inss1.mm"
include "a1i.mm"
include "estrcbas.mm"
include "eqcomd.mm"
include "3sstr4d.mm"
include "reschom.mm"
include "eqtr4d.mm"

theorem ringchomfval
  let wph: wff ph
  let cB: class B
  let cC: class C
  let cU: class U
  let cH: class H
  let cV: class V
  let vk: setvar k
  let vx: setvar x
  assume ringcbas.c: |- C = ( RingCat ` U )
  assume ringcbas.b: |- B = ( Base ` C )
  assume ringcbas.u: |- ( ph -> U e. V )
  assume ringchomfval.h: |- H = ( Hom ` C )


  assert |- ( ph -> H = ( RingHom |` ( B X. B ) ) )

  proof
    wph
    cH
    cU
    cestrc
    cfv
    #
    crh
    cB
    cB
    cxp
    cres
    #
    cresc
    co
    #
    chom
    cfv
    #
    @1
    wph
    cH
    cC
    chom
    cfv
    @3
    ringchomfval.h
    wph
    cC
    @2
    chom
    wph
    cB
    cC
    cU
    @1
    cV
    ringcbas.c
    ringcbas.u
    wph
    cB
    cC
    cU
    cV
    ringcbas.c
    ringcbas.b
    ringcbas.u
    ringcbas
    #
    wph
    @1
    eqidd
    #
    ringcval
    fveq2d
    syl5eq
    wph
    @0
    cbs
    cfv
    #
    @0
    @2
    cB
    @1
    cvv
    @2
    eqid
    @6
    eqid
    wph
    cU
    cestrc
    fvexd
    wph
    cB
    cU
    @1
    @4
    @5
    rhmresfn
    wph
    cU
    crg
    cin
    #
    cU
    cB
    @6
    @7
    cU
    wss
    wph
    cU
    crg
    inss1
    a1i
    @4
    wph
    cU
    @6
    wph
    @0
    cU
    cV
    @0
    eqid
    ringcbas.u
    estrcbas
    eqcomd
    3sstr4d
    reschom
    eqtr4d
end
