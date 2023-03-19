include "cn0.mm"
include "wcel.mm"
include "cr.mm"
include "c2.mm"
include "cle.mm"
include "wbr.mm"
include "w3a.mm"
include "cn.mm"
include "cexp.mm"
include "co.mm"
include "cc0.mm"
include "wceq.mm"
include "wa.mm"
include "simpr.mm"
include "simpl2.mm"
include "simpl3.mm"
include "cv.mm"
include "wi.mm"
include "c1.mm"
include "caddc.mm"
include "id.mm"
include "oveq2.mm"
include "breq12d.mm"
include "imbi2d.mm"
include "simpl.mm"
include "1nn0.mm"
include "a1i.mm"
include "1red.mm"
include "2re.mm"
include "1le2.mm"
include "letrd.mm"
include "expge1d.mm"
include "cmul.mm"
include "simp1.mm"
include "nnnn0d.mm"
include "nn0red.mm"
include "readdcld.mm"
include "3ad2ant2.mm"
include "remulcld.mm"
include "reexpcld.mm"
include "nnge1d.mm"
include "leadd2dd.mm"
include "recnd.mm"
include "times2d.mm"
include "breqtrrd.mm"
include "nn0ge0d.mm"
include "simp2r.mm"
include "lemul2ad.mm"
include "0red.mm"
include "0le2.mm"
include "simp3.mm"
include "lemul1ad.mm"
include "expp1d.mm"
include "3exp.mm"
include "a2d.mm"
include "nnind.mm"
include "3impib.mm"
include "syl3anc.mm"
include "0le1.mm"
include "oveq2d.mm"
include "exp0d.mm"
include "eqtrd.mm"
include "3brtr4d.mm"
include "wo.mm"
include "elnn0.mm"
include "biimpi.mm"
include "3ad2ant1.mm"
include "mpjaodan.mm"

theorem nexple
  let cA: class A
  let cB: class B
  let vk: setvar k
  let vn: setvar n


  assert |- ( ( A e. NN0 /\ B e. RR /\ 2 <_ B ) -> A <_ ( B ^ A ) )

  proof
    cA
    cn0
    wcel
    #
    cB
    cr
    wcel
    #
    c2
    cB
    cle
    wbr
    #
    w3a
    #
    cA
    cn
    wcel
    #
    cA
    cB
    cA
    cexp
    co
    #
    cle
    wbr
    #
    cA
    cc0
    wceq
    #
    @3
    @4
    wa
    @4
    @1
    @2
    @6
    @3
    @4
    simpr
    @0
    @1
    @2
    @4
    simpl2
    @0
    @1
    @2
    @4
    simpl3
    @4
    @1
    @2
    @6
    @1
    @2
    wa
    #
    vk
    cv
    #
    cB
    @9
    cexp
    co
    #
    cle
    wbr
    #
    wi
    @8
    c1
    cB
    c1
    cexp
    co
    #
    cle
    wbr
    #
    wi
    @8
    vn
    cv
    #
    cB
    @14
    cexp
    co
    #
    cle
    wbr
    #
    wi
    @8
    @14
    c1
    caddc
    co
    #
    cB
    @17
    cexp
    co
    #
    cle
    wbr
    #
    wi
    @8
    @6
    wi
    vk
    vn
    cA
    @9
    c1
    wceq
    #
    @11
    @13
    @8
    @20
    @9
    c1
    @10
    @12
    cle
    @20
    id
    @9
    c1
    cB
    cexp
    oveq2
    breq12d
    imbi2d
    @9
    @14
    wceq
    #
    @11
    @16
    @8
    @21
    @9
    @14
    @10
    @15
    cle
    @21
    id
    @9
    @14
    cB
    cexp
    oveq2
    breq12d
    imbi2d
    @9
    @17
    wceq
    #
    @11
    @19
    @8
    @22
    @9
    @17
    @10
    @18
    cle
    @22
    id
    @9
    @17
    cB
    cexp
    oveq2
    breq12d
    imbi2d
    @9
    cA
    wceq
    #
    @11
    @6
    @8
    @23
    @9
    cA
    @10
    @5
    cle
    @23
    id
    @9
    cA
    cB
    cexp
    oveq2
    breq12d
    imbi2d
    @8
    cB
    c1
    @1
    @2
    simpl
    #
    c1
    cn0
    wcel
    @8
    1nn0
    a1i
    @8
    c1
    c2
    cB
    @8
    1red
    c2
    cr
    wcel
    #
    @8
    2re
    a1i
    #
    @24
    c1
    c2
    cle
    wbr
    @8
    1le2
    a1i
    @1
    @2
    simpr
    #
    letrd
    expge1d
    @14
    cn
    wcel
    #
    @8
    @16
    @19
    @28
    @8
    @16
    @19
    @28
    @8
    @16
    w3a
    #
    @17
    @15
    cB
    cmul
    co
    #
    @18
    cle
    @29
    @17
    @14
    cB
    cmul
    co
    #
    @30
    @29
    @14
    c1
    @29
    @14
    @29
    @14
    @28
    @8
    @16
    simp1
    #
    nnnn0d
    #
    nn0red
    #
    @29
    1red
    #
    readdcld
    #
    @29
    @14
    cB
    @34
    @8
    @28
    @1
    @16
    @24
    3ad2ant2
    #
    remulcld
    #
    @29
    @15
    cB
    @29
    cB
    @14
    @37
    @33
    reexpcld
    #
    @37
    remulcld
    @29
    @17
    @14
    c2
    cmul
    co
    #
    @31
    @36
    @29
    @14
    c2
    @34
    @25
    @29
    2re
    a1i
    #
    remulcld
    @38
    @29
    @17
    @14
    @14
    caddc
    co
    @40
    cle
    @29
    c1
    @14
    @14
    @35
    @34
    @34
    @29
    @14
    @32
    nnge1d
    leadd2dd
    @29
    @14
    @29
    @14
    @34
    recnd
    times2d
    breqtrrd
    @29
    c2
    cB
    @14
    @41
    @37
    @34
    @29
    @14
    @33
    nn0ge0d
    @28
    @1
    @2
    @16
    simp2r
    lemul2ad
    letrd
    @29
    @14
    @15
    cB
    @34
    @39
    @37
    @8
    @28
    cc0
    cB
    cle
    wbr
    @16
    @8
    cc0
    c2
    cB
    @8
    0red
    @26
    @24
    cc0
    c2
    cle
    wbr
    @8
    0le2
    a1i
    @27
    letrd
    3ad2ant2
    @28
    @8
    @16
    simp3
    lemul1ad
    letrd
    @29
    cB
    @14
    @29
    cB
    @37
    recnd
    @33
    expp1d
    breqtrrd
    3exp
    a2d
    nnind
    3impib
    syl3anc
    @3
    @7
    wa
    #
    cc0
    c1
    cA
    @5
    cle
    cc0
    c1
    cle
    wbr
    @42
    0le1
    a1i
    @3
    @7
    simpr
    #
    @42
    @5
    cB
    cc0
    cexp
    co
    c1
    @42
    cA
    cc0
    cB
    cexp
    @43
    oveq2d
    @42
    cB
    @42
    cB
    @0
    @1
    @2
    @7
    simpl2
    recnd
    exp0d
    eqtrd
    3brtr4d
    @0
    @1
    @4
    @7
    wo
    #
    @2
    @0
    @44
    cA
    elnn0
    biimpi
    3ad2ant1
    mpjaodan
end
