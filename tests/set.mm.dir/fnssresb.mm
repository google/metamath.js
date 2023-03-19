include "cres.mm"
include "wfn.mm"
include "wfun.mm"
include "cdm.mm"
include "wceq.mm"
include "wa.mm"
include "wss.mm"
include "df-fn.mm"
include "fnfun.mm"
include "funres.mm"
include "syl.mm"
include "biantrurd.mm"
include "ssdmres.mm"
include "fndm.mm"
include "sseq2d.mm"
include "syl5bbr.mm"
include "bitr3d.mm"
include "syl5bb.mm"

theorem fnssresb
  let cA: class A
  let cB: class B
  let cF: class F


  assert |- ( F Fn A -> ( ( F |` B ) Fn B <-> B C_ A ) )

  proof
    cF
    cB
    cres
    #
    cB
    wfn
    @0
    wfun
    #
    @0
    cdm
    cB
    wceq
    #
    wa
    #
    cF
    cA
    wfn
    #
    cB
    cA
    wss
    #
    @0
    cB
    df-fn
    @4
    @2
    @3
    @5
    @4
    @1
    @2
    @4
    cF
    wfun
    @1
    cA
    cF
    fnfun
    cB
    cF
    funres
    syl
    biantrurd
    @2
    cB
    cF
    cdm
    #
    wss
    @4
    @5
    cB
    cF
    ssdmres
    @4
    @6
    cA
    cB
    cA
    cF
    fndm
    sseq2d
    syl5bbr
    bitr3d
    syl5bb
end
