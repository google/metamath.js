include "wcel.mm"
include "wa.mm"
include "csn.mm"
include "ccda.mm"
include "co.mm"
include "ccnv.mm"
include "c2o.mm"
include "wfn.mm"
include "c0.mm"
include "cop.mm"
include "c1o.mm"
include "cpr.mm"
include "cvv.mm"
include "con0.mm"
include "0ex.mm"
include "1on.mm"
include "wne.mm"
include "1n0.mm"
include "necomi.mm"
include "fnprg.mm"
include "mp3an3.mm"
include "mpanl12.mm"
include "df2o3.mm"
include "fneq2i.mm"
include "sylibr.mm"
include "xpscg.mm"
include "fneq1d.mm"
include "mpbird.mm"

theorem xpscfn
  let cA: class A
  let cB: class B
  let cV: class V
  let cW: class W


  assert |- ( ( A e. V /\ B e. W ) -> `' ( { A } +c { B } ) Fn 2o )

  proof
    cA
    cV
    wcel
    cB
    cW
    wcel
    wa
    #
    cA
    csn
    cB
    csn
    ccda
    co
    ccnv
    #
    c2o
    wfn
    c0
    cA
    cop
    c1o
    cB
    cop
    cpr
    #
    c2o
    wfn
    #
    @0
    @2
    c0
    c1o
    cpr
    #
    wfn
    #
    @3
    c0
    cvv
    wcel
    #
    c1o
    con0
    wcel
    #
    @0
    @5
    0ex
    1on
    @6
    @7
    wa
    @0
    c0
    c1o
    wne
    @5
    c1o
    c0
    1n0
    necomi
    c0
    c1o
    cA
    cB
    cvv
    con0
    cV
    cW
    fnprg
    mp3an3
    mpanl12
    c2o
    @4
    @2
    df2o3
    fneq2i
    sylibr
    @0
    c2o
    @1
    @2
    cA
    cB
    cV
    cW
    xpscg
    fneq1d
    mpbird
end
