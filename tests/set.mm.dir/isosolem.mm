include "wiso.mm"
include "wpo.mm"
include "cv.mm"
include "wbr.mm"
include "weq.mm"
include "w3o.mm"
include "wral.mm"
include "wa.mm"
include "wor.mm"
include "isopolem.mm"
include "wcel.mm"
include "cfv.mm"
include "wceq.mm"
include "wi.mm"
include "wf1o.mm"
include "wf.mm"
include "isof1o.mm"
include "f1of.mm"
include "ffvelrn.mm"
include "ex.mm"
include "anim12d.mm"
include "3syl.mm"
include "imp.mm"
include "breq1.mm"
include "eqeq1.mm"
include "breq2.mm"
include "3orbi123d.mm"
include "eqeq2.mm"
include "rspc2v.mm"
include "syl.mm"
include "isorel.mm"
include "wf1.mm"
include "wb.mm"
include "f1of1.mm"
include "f1fveq.mm"
include "sylan.mm"
include "bicomd.mm"
include "ancom2s.mm"
include "sylibrd.mm"
include "ralrimdvva.mm"
include "df-so.mm"
include "3imtr4g.mm"

theorem isosolem
  let cA: class A
  let cB: class B
  let cR: class R
  let cS: class S
  let cH: class H
  let va: setvar a
  let vb: setvar b
  let vc: setvar c
  let vd: setvar d
  let ve: setvar e
  let vf: setvar f


  assert |- ( H Isom R , S ( A , B ) -> ( S Or B -> R Or A ) )

  proof
    cA
    cB
    cR
    cS
    cH
    wiso
    #
    cB
    cS
    wpo
    #
    va
    cv
    #
    vb
    cv
    #
    cS
    wbr
    #
    va
    vb
    weq
    #
    @3
    @2
    cS
    wbr
    #
    w3o
    #
    vb
    cB
    wral
    va
    cB
    wral
    #
    wa
    cA
    cR
    wpo
    #
    vc
    cv
    #
    vd
    cv
    #
    cR
    wbr
    #
    vc
    vd
    weq
    #
    @11
    @10
    cR
    wbr
    #
    w3o
    #
    vd
    cA
    wral
    vc
    cA
    wral
    #
    wa
    cB
    cS
    wor
    cA
    cR
    wor
    @0
    @1
    @9
    @8
    @16
    cA
    cB
    cR
    cS
    cH
    isopolem
    @0
    @8
    @15
    vc
    vd
    cA
    cA
    @0
    @10
    cA
    wcel
    #
    @11
    cA
    wcel
    #
    wa
    #
    wa
    #
    @8
    @10
    cH
    cfv
    #
    @11
    cH
    cfv
    #
    cS
    wbr
    #
    @21
    @22
    wceq
    #
    @22
    @21
    cS
    wbr
    #
    w3o
    #
    @15
    @20
    @21
    cB
    wcel
    #
    @22
    cB
    wcel
    #
    wa
    #
    @8
    @26
    wi
    @0
    @19
    @29
    @0
    cA
    cB
    cH
    wf1o
    #
    cA
    cB
    cH
    wf
    #
    @19
    @29
    wi
    cA
    cB
    cR
    cS
    cH
    isof1o
    #
    cA
    cB
    cH
    f1of
    @31
    @17
    @27
    @18
    @28
    @31
    @17
    @27
    cA
    cB
    @10
    cH
    ffvelrn
    ex
    @31
    @18
    @28
    cA
    cB
    @11
    cH
    ffvelrn
    ex
    anim12d
    3syl
    imp
    @7
    @26
    @21
    @3
    cS
    wbr
    #
    @21
    @3
    wceq
    #
    @3
    @21
    cS
    wbr
    #
    w3o
    va
    vb
    @21
    @22
    cB
    cB
    @2
    @21
    wceq
    @4
    @33
    @5
    @34
    @6
    @35
    @2
    @21
    @3
    cS
    breq1
    @2
    @21
    @3
    eqeq1
    @2
    @21
    @3
    cS
    breq2
    3orbi123d
    @3
    @22
    wceq
    @33
    @23
    @34
    @24
    @35
    @25
    @3
    @22
    @21
    cS
    breq2
    @3
    @22
    @21
    eqeq2
    @3
    @22
    @21
    cS
    breq1
    3orbi123d
    rspc2v
    syl
    @20
    @12
    @23
    @13
    @24
    @14
    @25
    cA
    cB
    @10
    @11
    cR
    cS
    cH
    isorel
    @20
    @24
    @13
    @0
    cA
    cB
    cH
    wf1
    #
    @19
    @24
    @13
    wb
    @0
    @30
    @36
    @32
    cA
    cB
    cH
    f1of1
    syl
    cA
    cB
    @10
    @11
    cH
    f1fveq
    sylan
    bicomd
    @0
    @18
    @17
    @14
    @25
    wb
    cA
    cB
    @11
    @10
    cR
    cS
    cH
    isorel
    ancom2s
    3orbi123d
    sylibrd
    ralrimdvva
    anim12d
    va
    vb
    cB
    cS
    df-so
    vc
    vd
    cA
    cR
    df-so
    3imtr4g
end
