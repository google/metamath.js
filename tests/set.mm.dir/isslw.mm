include "cslw.mm"
include "co.mm"
include "wcel.mm"
include "cprime.mm"
include "cgrp.mm"
include "wa.mm"
include "csubg.mm"
include "cfv.mm"
include "cv.mm"
include "wss.mm"
include "cress.mm"
include "cpgp.mm"
include "wbr.mm"
include "wceq.mm"
include "wb.mm"
include "wral.mm"
include "w3a.mm"
include "crab.mm"
include "df-slw.mm"
include "elmpt2cl.mm"
include "simp1.mm"
include "subgrcl.mm"
include "3ad2ant2.mm"
include "jca.mm"
include "simpr.mm"
include "fveq2d.mm"
include "simpl.mm"
include "oveq1d.mm"
include "breq12d.mm"
include "anbi2d.mm"
include "bibi1d.mm"
include "raleqbidv.mm"
include "rabeqbidv.mm"
include "fvex.mm"
include "rabex.mm"
include "ovmpt2a.mm"
include "eleq2d.mm"
include "sseq1.mm"
include "anbi1d.mm"
include "eqeq1.mm"
include "bibi12d.mm"
include "ralbidv.mm"
include "elrab.mm"
include "syl6bb.mm"
include "biantrurd.mm"
include "bitrd.mm"
include "3anass.mm"
include "syl6bbr.mm"
include "pm5.21nii.mm"

theorem isslw
  let cP: class P
  let vk: setvar k
  let cG: class G
  let cH: class H
  let vg: setvar g
  let vh: setvar h
  let vp: setvar p
  let cK: class K
  let cS: class S

  disjoint G k
  disjoint H k
  disjoint P k
  disjoint g h
  disjoint g k
  disjoint g p
  disjoint G g
  disjoint h k
  disjoint h p
  disjoint G h
  disjoint k p
  disjoint G p
  disjoint H h
  disjoint K k
  disjoint P g
  disjoint P h
  disjoint P p
  disjoint S k
  assert |- ( H e. ( P pSyl G ) <-> ( P e. Prime /\ H e. ( SubGrp ` G ) /\ A. k e. ( SubGrp ` G ) ( ( H C_ k /\ P pGrp ( G |`s k ) ) <-> H = k ) ) )

  proof
    cH
    cP
    cG
    cslw
    co
    #
    wcel
    #
    cP
    cprime
    wcel
    #
    cG
    cgrp
    wcel
    #
    wa
    #
    @2
    cH
    cG
    csubg
    cfv
    #
    wcel
    #
    cH
    vk
    cv
    #
    wss
    #
    cP
    cG
    @7
    cress
    co
    #
    cpgp
    wbr
    #
    wa
    #
    cH
    @7
    wceq
    #
    wb
    #
    vk
    @5
    wral
    #
    w3a
    #
    vp
    vg
    cprime
    cgrp
    vh
    cv
    #
    @7
    wss
    #
    vp
    cv
    #
    vg
    cv
    #
    @7
    cress
    co
    #
    cpgp
    wbr
    #
    wa
    #
    @16
    @7
    wceq
    #
    wb
    #
    vk
    @19
    csubg
    cfv
    #
    wral
    #
    vh
    @25
    crab
    #
    cP
    cG
    cslw
    cH
    vg
    vh
    vk
    vp
    df-slw
    #
    elmpt2cl
    @15
    @2
    @3
    @2
    @6
    @14
    simp1
    @6
    @2
    @3
    @14
    cH
    cG
    subgrcl
    3ad2ant2
    jca
    @4
    @1
    @2
    @6
    @14
    wa
    #
    wa
    #
    @15
    @4
    @1
    @29
    @30
    @4
    @1
    cH
    @17
    @10
    wa
    #
    @23
    wb
    #
    vk
    @5
    wral
    #
    vh
    @5
    crab
    #
    wcel
    @29
    @4
    @0
    @34
    cH
    vp
    vg
    cP
    cG
    cprime
    cgrp
    @27
    @34
    cslw
    @18
    cP
    wceq
    #
    @19
    cG
    wceq
    #
    wa
    #
    @26
    @33
    vh
    @25
    @5
    @37
    @19
    cG
    csubg
    @35
    @36
    simpr
    #
    fveq2d
    #
    @37
    @24
    @32
    vk
    @25
    @5
    @39
    @37
    @22
    @31
    @23
    @37
    @21
    @10
    @17
    @37
    @18
    cP
    @20
    @9
    cpgp
    @35
    @36
    simpl
    @37
    @19
    cG
    @7
    cress
    @38
    oveq1d
    breq12d
    anbi2d
    bibi1d
    raleqbidv
    rabeqbidv
    @28
    @33
    vh
    @5
    cG
    csubg
    fvex
    rabex
    ovmpt2a
    eleq2d
    @33
    @14
    vh
    cH
    @5
    @16
    cH
    wceq
    #
    @32
    @13
    vk
    @5
    @40
    @31
    @11
    @23
    @12
    @40
    @17
    @8
    @10
    @16
    cH
    @7
    sseq1
    anbi1d
    @16
    cH
    @7
    eqeq1
    bibi12d
    ralbidv
    elrab
    syl6bb
    @4
    @2
    @29
    @2
    @3
    simpl
    biantrurd
    bitrd
    @2
    @6
    @14
    3anass
    syl6bbr
    pm5.21nii
end
