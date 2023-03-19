include "cz.mm"
include "wcel.mm"
include "cc.mm"
include "wf.mm"
include "wa.mm"
include "clm.mm"
include "cfv.mm"
include "wbr.mm"
include "cpm.mm"
include "co.mm"
include "cli.mm"
include "cdm.mm"
include "wss.mm"
include "wb.mm"
include "wceq.mm"
include "simpr.mm"
include "fdm.mm"
include "eqimss2.mm"
include "3syl.mm"
include "lmclim.mm"
include "syldan.mm"
include "cuz.mm"
include "uzssz.mm"
include "zsscn.mm"
include "sstri.mm"
include "eqsstri.mm"
include "cvv.mm"
include "cnex.mm"
include "elpm2r.mm"
include "mpanl12.mm"
include "sylancl.mm"
include "biantrurd.mm"
include "bitr4d.mm"

theorem lmclimf
  let cP: class P
  let cF: class F
  let cJ: class J
  let cM: class M
  let cZ: class Z
  let vj: setvar j
  let vk: setvar k
  let vx: setvar x
  assume lmclim.2: |- J = ( TopOpen ` CCfld )
  assume lmclim.3: |- Z = ( ZZ>= ` M )


  assert |- ( ( M e. ZZ /\ F : Z --> CC ) -> ( F ( ~~>t ` J ) P <-> F ~~> P ) )

  proof
    cM
    cz
    wcel
    #
    cZ
    cc
    cF
    wf
    #
    wa
    #
    cF
    cP
    cJ
    clm
    cfv
    wbr
    #
    cF
    cc
    cc
    cpm
    co
    wcel
    #
    cF
    cP
    cli
    wbr
    #
    wa
    #
    @5
    @0
    @1
    cZ
    cF
    cdm
    #
    wss
    #
    @3
    @6
    wb
    @2
    @1
    @7
    cZ
    wceq
    @8
    @0
    @1
    simpr
    #
    cZ
    cc
    cF
    fdm
    cZ
    @7
    eqimss2
    3syl
    cP
    cF
    cJ
    cM
    cZ
    lmclim.2
    lmclim.3
    lmclim
    syldan
    @2
    @4
    @5
    @2
    @1
    cZ
    cc
    wss
    #
    @4
    @9
    cZ
    cM
    cuz
    cfv
    #
    cc
    lmclim.3
    @11
    cz
    cc
    cM
    uzssz
    zsscn
    sstri
    eqsstri
    cc
    cvv
    wcel
    #
    @12
    @1
    @10
    wa
    @4
    cnex
    cnex
    cc
    cc
    cZ
    cF
    cvv
    cvv
    elpm2r
    mpanl12
    sylancl
    biantrurd
    bitr4d
end
