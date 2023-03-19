include "cestrc.mm"
include "cfv.mm"
include "crngh.mm"
include "cxp.mm"
include "cres.mm"
include "cresc.mm"
include "co.mm"
include "chom.mm"
include "rngcbas.mm"
include "eqidd.mm"
include "rngcval.mm"
include "fveq2d.mm"
include "syl5eq.mm"
include "cbs.mm"
include "cvv.mm"
include "eqid.mm"
include "fvexd.mm"
include "rnghmresfn.mm"
include "crng.mm"
include "cin.mm"
include "wss.mm"
include "inss1.mm"
include "a1i.mm"
include "estrcbas.mm"
include "eqcomd.mm"
include "3sstr4d.mm"
include "reschom.mm"
include "eqtr4d.mm"

theorem rngchomfval
  let wph: wff ph
  let cB: class B
  let cC: class C
  let cU: class U
  let cH: class H
  let cV: class V
  let vk: setvar k
  let vx: setvar x
  assume rngcbas.c: |- C = ( RngCat ` U )
  assume rngcbas.b: |- B = ( Base ` C )
  assume rngcbas.u: |- ( ph -> U e. V )
  assume rngchomfval.h: |- H = ( Hom ` C )


  assert |- ( ph -> H = ( RngHomo |` ( B X. B ) ) )

  proof
    wph
    cH
    cU
    cestrc
    cfv
    #
    crngh
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
    rngchomfval.h
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
    rngcbas.c
    rngcbas.u
    wph
    cB
    cC
    cU
    cV
    rngcbas.c
    rngcbas.b
    rngcbas.u
    rngcbas
    #
    wph
    @1
    eqidd
    #
    rngcval
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
    rnghmresfn
    wph
    cU
    crng
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
    crng
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
    rngcbas.u
    estrcbas
    eqcomd
    3sstr4d
    reschom
    eqtr4d
end
