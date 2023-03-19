include "wcel.mm"
include "cpw.mm"
include "c0.mm"
include "csn.mm"
include "cpr.mm"
include "cmap.mm"
include "co.mm"
include "c2o.mm"
include "cen.mm"
include "cvv.mm"
include "wel.mm"
include "cif.mm"
include "cmpt.mm"
include "wf1o.mm"
include "wbr.mm"
include "pwexg.mm"
include "ovexd.mm"
include "id.mm"
include "0ex.mm"
include "a1i.mm"
include "p0ex.mm"
include "wne.mm"
include "0nep0.mm"
include "eqid.mm"
include "pw2f1o.mm"
include "f1oen2g.mm"
include "syl3anc.mm"
include "df2o2.mm"
include "oveq1i.mm"
include "syl6breqr.mm"

theorem pw2eng
  let cA: class A
  let cV: class V
  let vx: setvar x
  let vz: setvar z


  assert |- ( A e. V -> ~P A ~~ ( 2o ^m A ) )

  proof
    cA
    cV
    wcel
    #
    cA
    cpw
    #
    c0
    c0
    csn
    #
    cpr
    #
    cA
    cmap
    co
    #
    c2o
    cA
    cmap
    co
    cen
    @0
    @1
    cvv
    wcel
    @4
    cvv
    wcel
    @1
    @4
    vx
    @1
    vz
    cA
    vz
    vx
    wel
    @2
    c0
    cif
    cmpt
    cmpt
    #
    wf1o
    @1
    @4
    cen
    wbr
    cA
    cV
    pwexg
    @0
    @3
    cA
    cmap
    ovexd
    @0
    vx
    vz
    cA
    c0
    @2
    @5
    cV
    cvv
    @0
    id
    c0
    cvv
    wcel
    @0
    0ex
    a1i
    @2
    cvv
    wcel
    @0
    p0ex
    a1i
    c0
    @2
    wne
    @0
    0nep0
    a1i
    @5
    eqid
    pw2f1o
    @1
    @4
    @5
    cvv
    cvv
    f1oen2g
    syl3anc
    c2o
    @3
    cA
    cmap
    df2o2
    oveq1i
    syl6breqr
end
