include "wrel.mm"
include "wf.mm"
include "ccnv.mm"
include "ctpos.mm"
include "wa.mm"
include "crn.mm"
include "wfo.mm"
include "wfn.mm"
include "ffn.mm"
include "dffn4.mm"
include "sylib.mm"
include "tposfo2.mm"
include "syl5.mm"
include "imp.mm"
include "fof.mm"
include "syl.mm"
include "wss.mm"
include "frn.mm"
include "adantl.mm"
include "fssd.mm"
include "ex.mm"

theorem tposf2
  let cA: class A
  let cB: class B
  let cF: class F
  let vx: setvar x
  let vy: setvar y
  let vw: setvar w
  let vz: setvar z
  let cG: class G


  assert |- ( Rel A -> ( F : A --> B -> tpos F : `' A --> B ) )

  proof
    cA
    wrel
    #
    cA
    cB
    cF
    wf
    #
    cA
    ccnv
    #
    cB
    cF
    ctpos
    #
    wf
    @0
    @1
    wa
    #
    @2
    cF
    crn
    #
    cB
    @3
    @4
    @2
    @5
    @3
    wfo
    #
    @2
    @5
    @3
    wf
    @0
    @1
    @6
    @1
    cA
    @5
    cF
    wfo
    #
    @0
    @6
    @1
    cF
    cA
    wfn
    @7
    cA
    cB
    cF
    ffn
    cA
    cF
    dffn4
    sylib
    cA
    @5
    cF
    tposfo2
    syl5
    imp
    @2
    @5
    @3
    fof
    syl
    @1
    @5
    cB
    wss
    @0
    cA
    cB
    cF
    frn
    adantl
    fssd
    ex
end
