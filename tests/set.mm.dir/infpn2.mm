include "cn.mm"
include "wss.mm"
include "cv.mm"
include "clt.mm"
include "wbr.mm"
include "wrex.mm"
include "wral.mm"
include "cen.mm"
include "c1.mm"
include "cdiv.mm"
include "co.mm"
include "wcel.mm"
include "wceq.mm"
include "weq.mm"
include "wo.mm"
include "wi.mm"
include "wa.mm"
include "crab.mm"
include "ssrab2.mm"
include "eqsstri.mm"
include "infpn.mm"
include "cle.mm"
include "nnge1.mm"
include "adantr.mm"
include "cr.mm"
include "nnre.mm"
include "1re.mm"
include "lelttr.mm"
include "mp3an1.mm"
include "syl2an.mm"
include "mpand.mm"
include "ancld.mm"
include "anim1d.mm"
include "anass.mm"
include "syl6ib.mm"
include "reximdva.mm"
include "mpd.mm"
include "breq2.mm"
include "oveq1.mm"
include "eleq1d.mm"
include "equequ2.mm"
include "orbi2d.mm"
include "imbi12d.mm"
include "ralbidv.mm"
include "anbi12d.mm"
include "elrab2.mm"
include "anbi1i.mm"
include "ancom.mm"
include "anbi2i.mm"
include "3bitri.mm"
include "rexbii2.mm"
include "sylibr.mm"
include "rgen.mm"
include "unben.mm"
include "mp2an.mm"

theorem infpn2
  let cS: class S
  let vm: setvar m
  let vn: setvar n
  let vj: setvar j
  let vk: setvar k
  assume infpn2.1: |- S = { n e. NN | ( 1 < n /\ A. m e. NN ( ( n / m ) e. NN -> ( m = 1 \/ m = n ) ) ) }

  disjoint m n
  disjoint j k
  disjoint j n
  disjoint j m
  disjoint k n
  disjoint k m
  disjoint S j
  disjoint S k
  assert |- S ~~ NN

  proof
    cS
    cn
    wss
    vj
    cv
    #
    vk
    cv
    #
    clt
    wbr
    #
    vk
    cS
    wrex
    #
    vj
    cn
    wral
    cS
    cn
    cen
    wbr
    cS
    c1
    vn
    cv
    #
    clt
    wbr
    #
    @4
    vm
    cv
    #
    cdiv
    co
    #
    cn
    wcel
    #
    @6
    c1
    wceq
    #
    vm
    vn
    weq
    #
    wo
    #
    wi
    #
    vm
    cn
    wral
    #
    wa
    #
    vn
    cn
    crab
    cn
    infpn2.1
    @14
    vn
    cn
    ssrab2
    eqsstri
    @3
    vj
    cn
    @0
    cn
    wcel
    #
    @2
    c1
    @1
    clt
    wbr
    #
    @1
    @6
    cdiv
    co
    #
    cn
    wcel
    #
    @9
    vm
    vk
    weq
    #
    wo
    #
    wi
    #
    vm
    cn
    wral
    #
    wa
    #
    wa
    #
    vk
    cn
    wrex
    #
    @3
    @15
    @2
    @22
    wa
    #
    vk
    cn
    wrex
    @25
    vk
    vm
    @0
    infpn
    @15
    @26
    @24
    vk
    cn
    @15
    @1
    cn
    wcel
    #
    wa
    #
    @26
    @2
    @16
    wa
    #
    @22
    wa
    @24
    @28
    @2
    @29
    @22
    @28
    @2
    @16
    @28
    c1
    @0
    cle
    wbr
    #
    @2
    @16
    @15
    @30
    @27
    @0
    nnge1
    adantr
    @15
    @0
    cr
    wcel
    #
    @1
    cr
    wcel
    #
    @30
    @2
    wa
    @16
    wi
    #
    @27
    @0
    nnre
    @1
    nnre
    c1
    cr
    wcel
    @31
    @32
    @33
    1re
    c1
    @0
    @1
    lelttr
    mp3an1
    syl2an
    mpand
    ancld
    anim1d
    @2
    @16
    @22
    anass
    syl6ib
    reximdva
    mpd
    @2
    @24
    vk
    cS
    cn
    @1
    cS
    wcel
    #
    @2
    wa
    @27
    @23
    wa
    #
    @2
    wa
    @27
    @23
    @2
    wa
    #
    wa
    @27
    @24
    wa
    @34
    @35
    @2
    @14
    @23
    vn
    @1
    cn
    cS
    vn
    vk
    weq
    #
    @5
    @16
    @13
    @22
    @4
    @1
    c1
    clt
    breq2
    @37
    @12
    @21
    vm
    cn
    @37
    @8
    @18
    @11
    @20
    @37
    @7
    @17
    cn
    @4
    @1
    @6
    cdiv
    oveq1
    eleq1d
    @37
    @10
    @19
    @9
    vn
    vk
    vm
    equequ2
    orbi2d
    imbi12d
    ralbidv
    anbi12d
    infpn2.1
    elrab2
    anbi1i
    @27
    @23
    @2
    anass
    @36
    @24
    @27
    @23
    @2
    ancom
    anbi2i
    3bitri
    rexbii2
    sylibr
    rgen
    cS
    vj
    vk
    unben
    mp2an
end
