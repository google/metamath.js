include "cn.mm"
include "wcel.mm"
include "cz.mm"
include "wss.mm"
include "cfn.mm"
include "cc0.mm"
include "wnel.mm"
include "w3a.mm"
include "wa.mm"
include "clcmf.mm"
include "cfv.mm"
include "wceq.mm"
include "cv.mm"
include "cdvds.mm"
include "wbr.mm"
include "wral.mm"
include "cle.mm"
include "wi.mm"
include "dvdslcmf.mm"
include "3adant3.mm"
include "lcmfledvds.mm"
include "expdimp.mm"
include "ralrimiva.mm"
include "jca.mm"
include "adantl.mm"
include "breq2.mm"
include "ralbidv.mm"
include "breq1.mm"
include "imbi2d.mm"
include "anbi12d.mm"
include "syl5ibrcom.mm"
include "lcmfn0cl.mm"
include "imbi12d.mm"
include "rspcv.mm"
include "syl.mm"
include "adantld.mm"
include "clt.mm"
include "wo.mm"
include "cr.mm"
include "wb.mm"
include "nnre.mm"
include "nnred.mm"
include "anim12i.mm"
include "leloe.mm"
include "expd.mm"
include "impcom.mm"
include "wn.mm"
include "lenlt.mm"
include "syl2anr.mm"
include "pm2.21.mm"
include "syl6bi.mm"
include "syldc.mm"
include "adantr.mm"
include "com13.mm"
include "2a1.mm"
include "jaoi.mm"
include "com12.mm"
include "sylbid.mm"
include "embantd.mm"
include "com23.mm"
include "mpdd.mm"
include "impbid.mm"

theorem lcmf
  let vk: setvar k
  let vm: setvar m
  let cK: class K
  let cZ: class Z

  disjoint K k
  disjoint K m
  disjoint k m
  disjoint Z k
  disjoint Z m
  assert |- ( ( K e. NN /\ ( Z C_ ZZ /\ Z e. Fin /\ 0 e/ Z ) ) -> ( K = ( _lcm ` Z ) <-> ( A. m e. Z m || K /\ A. k e. NN ( A. m e. Z m || k -> K <_ k ) ) ) )

  proof
    cK
    cn
    wcel
    #
    cZ
    cz
    wss
    #
    cZ
    cfn
    wcel
    #
    cc0
    cZ
    wnel
    #
    w3a
    #
    wa
    #
    cK
    cZ
    clcmf
    cfv
    #
    wceq
    #
    vm
    cv
    #
    cK
    cdvds
    wbr
    #
    vm
    cZ
    wral
    #
    @8
    vk
    cv
    #
    cdvds
    wbr
    #
    vm
    cZ
    wral
    #
    cK
    @11
    cle
    wbr
    #
    wi
    #
    vk
    cn
    wral
    #
    wa
    #
    @5
    @17
    @7
    @8
    @6
    cdvds
    wbr
    #
    vm
    cZ
    wral
    #
    @13
    @6
    @11
    cle
    wbr
    #
    wi
    #
    vk
    cn
    wral
    #
    wa
    #
    @4
    @23
    @0
    @4
    @19
    @22
    @1
    @2
    @19
    @3
    vm
    cZ
    dvdslcmf
    3adant3
    #
    @4
    @21
    vk
    cn
    @4
    @11
    cn
    wcel
    @13
    @20
    vm
    @11
    cZ
    lcmfledvds
    expdimp
    ralrimiva
    jca
    adantl
    @7
    @10
    @19
    @16
    @22
    @7
    @9
    @18
    vm
    cZ
    cK
    @6
    @8
    cdvds
    breq2
    ralbidv
    @7
    @15
    @21
    vk
    cn
    @7
    @14
    @20
    @13
    cK
    @6
    @11
    cle
    breq1
    imbi2d
    ralbidv
    anbi12d
    syl5ibrcom
    @5
    @17
    @19
    cK
    @6
    cle
    wbr
    #
    wi
    #
    @7
    @5
    @16
    @26
    @10
    @5
    @6
    cn
    wcel
    #
    @16
    @26
    wi
    @4
    @27
    @0
    cZ
    lcmfn0cl
    #
    adantl
    @15
    @26
    vk
    @6
    cn
    @11
    @6
    wceq
    #
    @13
    @19
    @14
    @25
    @29
    @12
    @18
    vm
    cZ
    @11
    @6
    @8
    cdvds
    breq2
    ralbidv
    @11
    @6
    cK
    cle
    breq2
    imbi12d
    rspcv
    syl
    adantld
    @5
    @26
    @17
    @7
    @5
    @19
    @25
    @17
    @7
    wi
    #
    @4
    @19
    @0
    @24
    adantl
    @5
    @25
    cK
    @6
    clt
    wbr
    #
    @7
    wo
    #
    @30
    @5
    cK
    cr
    wcel
    #
    @6
    cr
    wcel
    #
    wa
    @25
    @32
    wb
    @0
    @33
    @4
    @34
    cK
    nnre
    #
    @4
    @6
    @28
    nnred
    #
    anim12i
    cK
    @6
    leloe
    syl
    @32
    @5
    @30
    @31
    @5
    @30
    wi
    @7
    @17
    @5
    @31
    @7
    @10
    @5
    @31
    @7
    wi
    #
    wi
    @16
    @5
    @10
    @6
    cK
    cle
    wbr
    #
    @37
    @4
    @0
    @10
    @38
    wi
    @4
    @0
    @10
    @38
    vm
    cK
    cZ
    lcmfledvds
    expd
    impcom
    @5
    @38
    @31
    wn
    #
    @37
    @4
    @34
    @33
    @38
    @39
    wb
    @0
    @36
    @35
    @6
    cK
    lenlt
    syl2anr
    @31
    @7
    pm2.21
    syl6bi
    syldc
    adantr
    com13
    @7
    @5
    @17
    2a1
    jaoi
    com12
    sylbid
    embantd
    com23
    mpdd
    impbid
end
