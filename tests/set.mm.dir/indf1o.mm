include "wcel.mm"
include "cpw.mm"
include "cc0.mm"
include "c1.mm"
include "cpr.mm"
include "cmap.mm"
include "co.mm"
include "cind.mm"
include "cfv.mm"
include "wf1o.mm"
include "wel.mm"
include "cif.mm"
include "cmpt.mm"
include "cr.mm"
include "id.mm"
include "0red.mm"
include "1red.mm"
include "wne.mm"
include "0ne1.mm"
include "a1i.mm"
include "eqid.mm"
include "pw2f1o.mm"
include "wceq.mm"
include "wb.mm"
include "indv.mm"
include "f1oeq1.mm"
include "syl.mm"
include "mpbird.mm"

theorem indf1o
  let cO: class O
  let cV: class V
  let va: setvar a
  let vx: setvar x


  assert |- ( O e. V -> ( _Ind ` O ) : ~P O -1-1-onto-> ( { 0 , 1 } ^m O ) )

  proof
    cO
    cV
    wcel
    #
    cO
    cpw
    #
    cc0
    c1
    cpr
    cO
    cmap
    co
    #
    cO
    cind
    cfv
    #
    wf1o
    #
    @1
    @2
    va
    @1
    vx
    cO
    vx
    va
    wel
    c1
    cc0
    cif
    cmpt
    cmpt
    #
    wf1o
    #
    @0
    va
    vx
    cO
    cc0
    c1
    @5
    cV
    cr
    @0
    id
    @0
    0red
    @0
    1red
    cc0
    c1
    wne
    @0
    0ne1
    a1i
    @5
    eqid
    pw2f1o
    @0
    @3
    @5
    wceq
    @4
    @6
    wb
    vx
    cO
    cV
    va
    indv
    @1
    @2
    @3
    @5
    f1oeq1
    syl
    mpbird
end
