include "cplig.mm"
include "wcel.mm"
include "wa.mm"
include "wne.mm"
include "cv.mm"
include "wreu.mm"
include "wel.mm"
include "wi.mm"
include "wral.mm"
include "w3a.mm"
include "wrex.mm"
include "wn.mm"
include "isplig.mm"
include "ibi.mm"
include "simp1.mm"
include "wceq.mm"
include "simpl.mm"
include "simpr.mm"
include "neeq12d.mm"
include "eleq1.mm"
include "bi2anan9.mm"
include "reubidv.mm"
include "imbi12d.mm"
include "rspc2gv.mm"
include "com23.mm"
include "imp.mm"
include "com12.mm"
include "3syl.mm"

theorem eulplig
  let cA: class A
  let cB: class B
  let cP: class P
  let cG: class G
  let vl: setvar l
  let va: setvar a
  let vb: setvar b
  let vc: setvar c
  assume eulplig.1: |- P = U. G

  disjoint G l
  disjoint A l
  disjoint B l
  disjoint a b
  disjoint a c
  disjoint a l
  disjoint G a
  disjoint b c
  disjoint b l
  disjoint G b
  disjoint c l
  disjoint G c
  disjoint P a
  disjoint P b
  disjoint P c
  disjoint A a
  disjoint A b
  disjoint B a
  disjoint B b
  assert |- ( ( G e. Plig /\ ( ( A e. P /\ B e. P ) /\ A =/= B ) ) -> E! l e. G ( A e. l /\ B e. l ) )

  proof
    cG
    cplig
    wcel
    #
    cA
    cP
    wcel
    cB
    cP
    wcel
    wa
    #
    cA
    cB
    wne
    #
    wa
    #
    cA
    vl
    cv
    #
    wcel
    #
    cB
    @4
    wcel
    #
    wa
    #
    vl
    cG
    wreu
    #
    @0
    va
    cv
    #
    vb
    cv
    #
    wne
    #
    va
    vl
    wel
    #
    vb
    vl
    wel
    #
    wa
    #
    vl
    cG
    wreu
    #
    wi
    #
    vb
    cP
    wral
    va
    cP
    wral
    #
    @11
    @12
    @13
    w3a
    vb
    cP
    wrex
    va
    cP
    wrex
    vl
    cG
    wral
    #
    @12
    @13
    vc
    vl
    wel
    w3a
    wn
    vl
    cG
    wral
    vc
    cP
    wrex
    vb
    cP
    wrex
    va
    cP
    wrex
    #
    w3a
    #
    @17
    @3
    @8
    wi
    @0
    @20
    cplig
    cP
    cG
    va
    vb
    vc
    vl
    eulplig.1
    isplig
    ibi
    @17
    @18
    @19
    simp1
    @3
    @17
    @8
    @1
    @2
    @17
    @8
    wi
    @1
    @17
    @2
    @8
    @16
    @2
    @8
    wi
    va
    vb
    cA
    cB
    cP
    cP
    @9
    cA
    wceq
    #
    @10
    cB
    wceq
    #
    wa
    #
    @11
    @2
    @15
    @8
    @23
    @9
    cA
    @10
    cB
    @21
    @22
    simpl
    @21
    @22
    simpr
    neeq12d
    @23
    @14
    @7
    vl
    cG
    @21
    @12
    @5
    @22
    @13
    @6
    @9
    cA
    @4
    eleq1
    @10
    cB
    @4
    eleq1
    bi2anan9
    reubidv
    imbi12d
    rspc2gv
    com23
    imp
    com12
    3syl
    imp
end
