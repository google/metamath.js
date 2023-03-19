include "wcel.mm"
include "c1o.mm"
include "cmap.mm"
include "co.mm"
include "c0.mm"
include "csn.mm"
include "cxp.mm"
include "ovexd.mm"
include "cvv.mm"
include "df1o2.mm"
include "p0ex.mm"
include "eqeltri.mm"
include "a1i.mm"
include "cv.mm"
include "0ex.mm"
include "2a1i.mm"
include "xpexg.mm"
include "mpan2.mm"
include "a1d.mm"
include "wceq.mm"
include "wa.mm"
include "wb.mm"
include "el1o.mm"
include "wf.mm"
include "oveq1i.mm"
include "eleq2i.mm"
include "elmapg.mm"
include "mpan.mm"
include "syl5bb.mm"
include "fconst2.mm"
include "syl6rbb.mm"
include "anbi12d.mm"
include "ancom.mm"
include "en2d.mm"

theorem map1
  let cA: class A
  let cV: class V
  let vx: setvar x
  let vy: setvar y
  let cB: class B
  let cC: class C
  let cD: class D


  assert |- ( A e. V -> ( 1o ^m A ) ~~ 1o )

  proof
    cA
    cV
    wcel
    #
    vx
    vy
    c1o
    cA
    cmap
    co
    #
    c1o
    c0
    cA
    c0
    csn
    #
    cxp
    #
    @0
    c1o
    cA
    cmap
    ovexd
    c1o
    cvv
    wcel
    @0
    c1o
    @2
    cvv
    df1o2
    p0ex
    eqeltri
    a1i
    c0
    cvv
    wcel
    @0
    vx
    cv
    #
    @1
    wcel
    #
    0ex
    2a1i
    @0
    @3
    cvv
    wcel
    #
    vy
    cv
    #
    c1o
    wcel
    #
    @0
    @2
    cvv
    wcel
    #
    @6
    p0ex
    cA
    @2
    cV
    cvv
    xpexg
    mpan2
    a1d
    @0
    @8
    @4
    @3
    wceq
    #
    wa
    @7
    c0
    wceq
    #
    @5
    wa
    @5
    @11
    wa
    @0
    @8
    @11
    @10
    @5
    @8
    @11
    wb
    @0
    @7
    el1o
    a1i
    @0
    @5
    cA
    @2
    @4
    wf
    #
    @10
    @5
    @4
    @2
    cA
    cmap
    co
    #
    wcel
    #
    @0
    @12
    @1
    @13
    @4
    c1o
    @2
    cA
    cmap
    df1o2
    oveq1i
    eleq2i
    @9
    @0
    @14
    @12
    wb
    p0ex
    @2
    cA
    @4
    cvv
    cV
    elmapg
    mpan
    syl5bb
    cA
    c0
    @4
    0ex
    fconst2
    syl6rbb
    anbi12d
    @11
    @5
    ancom
    syl6rbb
    en2d
end
