include "wf.mm"
include "wfn.mm"
include "cv.mm"
include "cfv.mm"
include "cmpt.mm"
include "wceq.mm"
include "ffn.mm"
include "wcel.mm"
include "wa.mm"
include "copab.mm"
include "wbr.mm"
include "wrel.mm"
include "fnrel.mm"
include "nfcv.mm"
include "dfrel4.mm"
include "sylib.mm"
include "nffn.mm"
include "nfv.mm"
include "fnbr.mm"
include "ex.mm"
include "pm4.71rd.mm"
include "eqcom.mm"
include "fnbrfvb.mm"
include "syl5bb.mm"
include "pm5.32da.mm"
include "bitr4d.mm"
include "opabbid.mm"
include "eqtrd.mm"
include "df-mpt.mm"
include "syl6eqr.mm"
include "3syl.mm"

theorem feqmptdf
  let wph: wff ph
  let vx: setvar x
  let cA: class A
  let cB: class B
  let cF: class F
  let vy: setvar y
  assume feqmptdf.1: |- F/_ x A
  assume feqmptdf.2: |- F/_ x F
  assume feqmptdf.3: |- ( ph -> F : A --> B )


  assert |- ( ph -> F = ( x e. A |-> ( F ` x ) ) )

  proof
    wph
    cA
    cB
    cF
    wf
    cF
    cA
    wfn
    #
    cF
    vx
    cA
    vx
    cv
    #
    cF
    cfv
    #
    cmpt
    #
    wceq
    feqmptdf.3
    cA
    cB
    cF
    ffn
    @0
    cF
    @1
    cA
    wcel
    #
    vy
    cv
    #
    @2
    wceq
    #
    wa
    #
    vx
    vy
    copab
    #
    @3
    @0
    cF
    @1
    @5
    cF
    wbr
    #
    vx
    vy
    copab
    #
    @8
    @0
    cF
    wrel
    cF
    @10
    wceq
    cA
    cF
    fnrel
    vx
    vy
    cF
    feqmptdf.2
    vy
    cF
    nfcv
    dfrel4
    sylib
    @0
    @9
    @7
    vx
    vy
    vx
    cA
    cF
    feqmptdf.2
    feqmptdf.1
    nffn
    @0
    vy
    nfv
    @0
    @9
    @4
    @9
    wa
    @7
    @0
    @9
    @4
    @0
    @9
    @4
    cA
    @1
    @5
    cF
    fnbr
    ex
    pm4.71rd
    @0
    @4
    @6
    @9
    @6
    @2
    @5
    wceq
    @0
    @4
    wa
    @9
    @5
    @2
    eqcom
    cA
    @1
    @5
    cF
    fnbrfvb
    syl5bb
    pm5.32da
    bitr4d
    opabbid
    eqtrd
    vx
    vy
    cA
    @2
    df-mpt
    syl6eqr
    3syl
end
