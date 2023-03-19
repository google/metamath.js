include "cn0.mm"
include "wcel.mm"
include "c1o.mm"
include "cmap.mm"
include "co.mm"
include "wa.mm"
include "csn.mm"
include "cxp.mm"
include "cle.mm"
include "cofr.mm"
include "wbr.mm"
include "c0.mm"
include "cfv.mm"
include "wral.mm"
include "cc0.mm"
include "cfz.mm"
include "con0.mm"
include "cvv.mm"
include "1on.mm"
include "a1i.mm"
include "cv.mm"
include "fvexd.mm"
include "simpll.mm"
include "cmpt.mm"
include "wceq.mm"
include "df1o2.mm"
include "nn0ex.mm"
include "0ex.mm"
include "mapsnconst.mm"
include "adantl.mm"
include "fconstmpt.mm"
include "syl6eq.mm"
include "ofrfval2.mm"
include "wne.mm"
include "wb.mm"
include "1n0.mm"
include "r19.3rzv.mm"
include "mp1i.mm"
include "wf.mm"
include "elmapi.mm"
include "0lt1o.mm"
include "ffvelrn.mm"
include "sylancl.mm"
include "biantrurd.mm"
include "fznn0.mm"
include "adantr.mm"
include "bitr4d.mm"
include "3bitr2d.mm"

theorem coe1mul2lem1
  let cA: class A
  let cX: class X
  let va: setvar a


  assert |- ( ( A e. NN0 /\ X e. ( NN0 ^m 1o ) ) -> ( X oR <_ ( 1o X. { A } ) <-> ( X ` (/) ) e. ( 0 ... A ) ) )

  proof
    cA
    cn0
    wcel
    #
    cX
    cn0
    c1o
    cmap
    co
    wcel
    #
    wa
    #
    cX
    c1o
    cA
    csn
    cxp
    #
    cle
    cofr
    wbr
    c0
    cX
    cfv
    #
    cA
    cle
    wbr
    #
    va
    c1o
    wral
    #
    @5
    @4
    cc0
    cA
    cfz
    co
    wcel
    #
    @2
    va
    c1o
    @4
    cA
    cle
    cX
    @3
    con0
    cvv
    cn0
    c1o
    con0
    wcel
    @2
    1on
    a1i
    @2
    va
    cv
    c1o
    wcel
    #
    wa
    c0
    cX
    fvexd
    @0
    @1
    @8
    simpll
    @2
    cX
    c1o
    @4
    csn
    cxp
    #
    va
    c1o
    @4
    cmpt
    @1
    cX
    @9
    wceq
    @0
    cn0
    c1o
    cX
    c0
    df1o2
    nn0ex
    0ex
    mapsnconst
    adantl
    va
    c1o
    @4
    fconstmpt
    syl6eq
    @3
    va
    c1o
    cA
    cmpt
    wceq
    @2
    va
    c1o
    cA
    fconstmpt
    a1i
    ofrfval2
    c1o
    c0
    wne
    @5
    @6
    wb
    @2
    1n0
    @5
    va
    c1o
    r19.3rzv
    mp1i
    @2
    @5
    @4
    cn0
    wcel
    #
    @5
    wa
    #
    @7
    @2
    @10
    @5
    @1
    @10
    @0
    @1
    c1o
    cn0
    cX
    wf
    c0
    c1o
    wcel
    @10
    cX
    cn0
    c1o
    elmapi
    0lt1o
    c1o
    cn0
    c0
    cX
    ffvelrn
    sylancl
    adantl
    biantrurd
    @0
    @7
    @11
    wb
    @1
    @4
    cA
    fznn0
    adantr
    bitr4d
    3bitr2d
end
