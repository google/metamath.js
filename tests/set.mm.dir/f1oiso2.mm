include "wf1o.mm"
include "cv.mm"
include "cfv.mm"
include "wceq.mm"
include "wa.mm"
include "wbr.mm"
include "wrex.mm"
include "copab.mm"
include "wiso.mm"
include "wcel.mm"
include "ccnv.mm"
include "w3a.mm"
include "f1ocnvdm.mm"
include "adantrr.mm"
include "3adant3.mm"
include "adantrl.mm"
include "f1ocnvfv2.mm"
include "eqcomd.mm"
include "anim12dan.mm"
include "simp3.mm"
include "fveq2.mm"
include "eqeq2d.mm"
include "anbi2d.mm"
include "breq2.mm"
include "anbi12d.mm"
include "rspcev.mm"
include "syl12anc.mm"
include "anbi1d.mm"
include "breq1.mm"
include "rexbidv.mm"
include "syl2anc.mm"
include "3expib.mm"
include "simp3ll.mm"
include "simp1.mm"
include "simp2l.mm"
include "f1of.mm"
include "ffvelrnda.mm"
include "eqeltrd.mm"
include "simp3lr.mm"
include "simp2r.mm"
include "simp3r.mm"
include "wi.mm"
include "f1ocnvfv.mm"
include "mpd.mm"
include "3brtr4d.mm"
include "jca31.mm"
include "3exp.mm"
include "rexlimdvv.mm"
include "impbid.mm"
include "opabbidv.mm"
include "syl5eq.mm"
include "f1oiso.mm"
include "mpdan.mm"

theorem f1oiso2
  let vx: setvar x
  let vy: setvar y
  let cA: class A
  let cB: class B
  let cR: class R
  let cS: class S
  let cH: class H
  let vw: setvar w
  let vz: setvar z
  assume f1oiso2.1: |- S = { <. x , y >. | ( ( x e. B /\ y e. B ) /\ ( `' H ` x ) R ( `' H ` y ) ) }

  disjoint A x
  disjoint A y
  disjoint x y
  disjoint B x
  disjoint B y
  disjoint H x
  disjoint H y
  disjoint R x
  disjoint R y
  disjoint A w
  disjoint A z
  disjoint w x
  disjoint w y
  disjoint w z
  disjoint x z
  disjoint y z
  disjoint B w
  disjoint B z
  disjoint H w
  disjoint H z
  disjoint R w
  disjoint R z
  assert |- ( H : A -1-1-onto-> B -> H Isom R , S ( A , B ) )

  proof
    cA
    cB
    cH
    wf1o
    #
    cS
    vx
    cv
    #
    vz
    cv
    #
    cH
    cfv
    #
    wceq
    #
    vy
    cv
    #
    vw
    cv
    #
    cH
    cfv
    #
    wceq
    #
    wa
    #
    @2
    @6
    cR
    wbr
    #
    wa
    #
    vw
    cA
    wrex
    #
    vz
    cA
    wrex
    #
    vx
    vy
    copab
    #
    wceq
    cA
    cB
    cR
    cS
    cH
    wiso
    @0
    cS
    @1
    cB
    wcel
    #
    @5
    cB
    wcel
    #
    wa
    #
    @1
    cH
    ccnv
    #
    cfv
    #
    @5
    @18
    cfv
    #
    cR
    wbr
    #
    wa
    #
    vx
    vy
    copab
    @14
    f1oiso2.1
    @0
    @22
    @13
    vx
    vy
    @0
    @22
    @13
    @0
    @17
    @21
    @13
    @0
    @17
    @21
    w3a
    #
    @19
    cA
    wcel
    #
    @1
    @19
    cH
    cfv
    #
    wceq
    #
    @8
    wa
    #
    @19
    @6
    cR
    wbr
    #
    wa
    #
    vw
    cA
    wrex
    #
    @13
    @0
    @17
    @24
    @21
    @0
    @15
    @24
    @16
    cA
    cB
    @1
    cH
    f1ocnvdm
    adantrr
    3adant3
    @23
    @20
    cA
    wcel
    #
    @26
    @5
    @20
    cH
    cfv
    #
    wceq
    #
    wa
    #
    @21
    @30
    @0
    @17
    @31
    @21
    @0
    @16
    @31
    @15
    cA
    cB
    @5
    cH
    f1ocnvdm
    adantrl
    3adant3
    @0
    @17
    @34
    @21
    @0
    @15
    @26
    @16
    @33
    @0
    @15
    wa
    @25
    @1
    cA
    cB
    @1
    cH
    f1ocnvfv2
    eqcomd
    @0
    @16
    wa
    @32
    @5
    cA
    cB
    @5
    cH
    f1ocnvfv2
    eqcomd
    anim12dan
    3adant3
    @0
    @17
    @21
    simp3
    @29
    @34
    @21
    wa
    vw
    @20
    cA
    @6
    @20
    wceq
    #
    @27
    @34
    @28
    @21
    @35
    @8
    @33
    @26
    @35
    @7
    @32
    @5
    @6
    @20
    cH
    fveq2
    eqeq2d
    anbi2d
    @6
    @20
    @19
    cR
    breq2
    anbi12d
    rspcev
    syl12anc
    @12
    @30
    vz
    @19
    cA
    @2
    @19
    wceq
    #
    @11
    @29
    vw
    cA
    @36
    @9
    @27
    @10
    @28
    @36
    @4
    @26
    @8
    @36
    @3
    @25
    @1
    @2
    @19
    cH
    fveq2
    eqeq2d
    anbi1d
    @2
    @19
    @6
    cR
    breq1
    anbi12d
    rexbidv
    rspcev
    syl2anc
    3expib
    @0
    @11
    @22
    vz
    vw
    cA
    cA
    @0
    @2
    cA
    wcel
    #
    @6
    cA
    wcel
    #
    wa
    #
    @11
    @22
    @0
    @39
    @11
    w3a
    #
    @15
    @16
    @21
    @40
    @1
    @3
    cB
    @4
    @8
    @10
    @0
    @39
    simp3ll
    #
    @40
    @0
    @37
    @3
    cB
    wcel
    @0
    @39
    @11
    simp1
    #
    @0
    @37
    @38
    @11
    simp2l
    #
    @0
    cA
    cB
    @2
    cH
    cA
    cB
    cH
    f1of
    #
    ffvelrnda
    syl2anc
    eqeltrd
    @40
    @5
    @7
    cB
    @4
    @8
    @10
    @0
    @39
    simp3lr
    #
    @40
    @0
    @38
    @7
    cB
    wcel
    @42
    @0
    @37
    @38
    @11
    simp2r
    #
    @0
    cA
    cB
    @6
    cH
    @44
    ffvelrnda
    syl2anc
    eqeltrd
    @40
    @2
    @6
    @19
    @20
    cR
    @0
    @39
    @9
    @10
    simp3r
    @40
    @3
    @1
    wceq
    #
    @19
    @2
    wceq
    #
    @40
    @1
    @3
    @41
    eqcomd
    @40
    @0
    @37
    @47
    @48
    wi
    @42
    @43
    cA
    cB
    @2
    @1
    cH
    f1ocnvfv
    syl2anc
    mpd
    @40
    @7
    @5
    wceq
    #
    @20
    @6
    wceq
    #
    @40
    @5
    @7
    @45
    eqcomd
    @40
    @0
    @38
    @49
    @50
    wi
    @42
    @46
    cA
    cB
    @6
    @5
    cH
    f1ocnvfv
    syl2anc
    mpd
    3brtr4d
    jca31
    3exp
    rexlimdvv
    impbid
    opabbidv
    syl5eq
    vz
    vw
    vx
    vy
    cA
    cB
    cR
    cS
    cH
    f1oiso
    mpdan
end
