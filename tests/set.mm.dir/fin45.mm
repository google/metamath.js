include "cfin4.mm"
include "wcel.mm"
include "cfin5.mm"
include "c0.mm"
include "wne.mm"
include "ccda.mm"
include "co.mm"
include "cen.mm"
include "wbr.mm"
include "wa.mm"
include "wn.mm"
include "c1o.mm"
include "csdm.mm"
include "isfin4-3.mm"
include "cdom.mm"
include "simpl.mm"
include "cvv.mm"
include "wb.mm"
include "relen.mm"
include "brrelexi.mm"
include "adantl.mm"
include "0sdomg.mm"
include "syl.mm"
include "mpbird.mm"
include "0sdom1dom.mm"
include "sylib.mm"
include "cdadom2.mm"
include "domen2.mm"
include "domnsym.mm"
include "con2i.mm"
include "sylbi.mm"
include "isfin5-2.mm"

theorem fin45
  let cA: class A
  let va: setvar a
  let vb: setvar b
  let vc: setvar c
  let vd: setvar d
  let vf: setvar f
  let vg: setvar g
  let vx: setvar x
  let vy: setvar y
  let cB: class B
  let cV: class V


  assert |- ( A e. Fin4 -> A e. Fin5 )

  proof
    cA
    cfin4
    wcel
    #
    cA
    cfin5
    wcel
    cA
    c0
    wne
    #
    cA
    cA
    cA
    ccda
    co
    #
    cen
    wbr
    #
    wa
    #
    wn
    #
    @0
    cA
    cA
    c1o
    ccda
    co
    #
    csdm
    wbr
    #
    @5
    cA
    isfin4-3
    @4
    @7
    @4
    @6
    cA
    cdom
    wbr
    #
    @7
    wn
    @4
    @8
    @6
    @2
    cdom
    wbr
    #
    @4
    c1o
    cA
    cdom
    wbr
    #
    @9
    @4
    c0
    cA
    csdm
    wbr
    #
    @10
    @4
    @11
    @1
    @1
    @3
    simpl
    @4
    cA
    cvv
    wcel
    #
    @11
    @1
    wb
    @3
    @12
    @1
    cA
    @2
    cen
    relen
    brrelexi
    adantl
    cA
    cvv
    0sdomg
    syl
    mpbird
    cA
    0sdom1dom
    sylib
    c1o
    cA
    cA
    cdadom2
    syl
    @3
    @8
    @9
    wb
    @1
    cA
    @2
    @6
    domen2
    adantl
    mpbird
    @6
    cA
    domnsym
    syl
    con2i
    sylbi
    cA
    cfin4
    isfin5-2
    mpbird
end
