include "wfun.mm"
include "cdm.mm"
include "wcel.mm"
include "csn.mm"
include "cres.mm"
include "cfv.mm"
include "cop.mm"
include "wss.mm"
include "wa.mm"
include "wceq.mm"
include "wfn.mm"
include "funfn.mm"
include "fnressn.mm"
include "sylanb.mm"
include "eqimss.mm"
include "syl.mm"
include "wn.mm"
include "c0.mm"
include "cin.mm"
include "disjsn.mm"
include "wb.mm"
include "fnresdisj.mm"
include "sylbi.mm"
include "syl5bbr.mm"
include "biimpa.mm"
include "0ss.mm"
include "syl6eqss.mm"
include "pm2.61dan.mm"

theorem funressn
  let cB: class B
  let cF: class F
  let cA: class A
  let vx: setvar x
  let cC: class C


  assert |- ( Fun F -> ( F |` { B } ) C_ { <. B , ( F ` B ) >. } )

  proof
    cF
    wfun
    #
    cB
    cF
    cdm
    #
    wcel
    #
    cF
    cB
    csn
    #
    cres
    #
    cB
    cB
    cF
    cfv
    cop
    csn
    #
    wss
    #
    @0
    @2
    wa
    @4
    @5
    wceq
    #
    @6
    @0
    cF
    @1
    wfn
    #
    @2
    @7
    cF
    funfn
    #
    @1
    cB
    cF
    fnressn
    sylanb
    @4
    @5
    eqimss
    syl
    @0
    @2
    wn
    #
    wa
    @4
    c0
    @5
    @0
    @10
    @4
    c0
    wceq
    #
    @10
    @1
    @3
    cin
    c0
    wceq
    #
    @0
    @11
    @1
    cB
    disjsn
    @0
    @8
    @12
    @11
    wb
    @9
    @1
    @3
    cF
    fnresdisj
    sylbi
    syl5bbr
    biimpa
    @5
    0ss
    syl6eqss
    pm2.61dan
end
