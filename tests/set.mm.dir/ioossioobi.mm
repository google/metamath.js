include "cioo.mm"
include "co.mm"
include "wss.mm"
include "cle.mm"
include "wbr.mm"
include "wa.mm"
include "cxr.mm"
include "clt.mm"
include "cinf.mm"
include "simpr.mm"
include "df-ioo.mm"
include "ixxssxr.mm"
include "infxrss.mm"
include "sylancl.mm"
include "wcel.mm"
include "c0.mm"
include "wne.mm"
include "wceq.mm"
include "adantr.mm"
include "wb.mm"
include "ioon0.mm"
include "syl2anc.mm"
include "mpbird.mm"
include "ssn0.mm"
include "cv.mm"
include "idd.mm"
include "xrltle.mm"
include "ixxlb.mm"
include "syl3anc.mm"
include "3brtr3d.mm"
include "csup.mm"
include "supxrss.mm"
include "ixxub.mm"
include "jca.mm"
include "simprl.mm"
include "simprr.mm"
include "ioossioo.mm"
include "syl22anc.mm"
include "impbida.mm"

theorem ioossioobi
  let wph: wff ph
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D
  let vw: setvar w
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  assume ioossioobi.a: |- ( ph -> A e. RR* )
  assume ioossioobi.b: |- ( ph -> B e. RR* )
  assume ioossioobi.c: |- ( ph -> C e. RR* )
  assume ioossioobi.d: |- ( ph -> D e. RR* )
  assume ioossioobi.cltd: |- ( ph -> C < D )


  assert |- ( ph -> ( ( C (,) D ) C_ ( A (,) B ) <-> ( A <_ C /\ D <_ B ) ) )

  proof
    wph
    cC
    cD
    cioo
    co
    #
    cA
    cB
    cioo
    co
    #
    wss
    #
    cA
    cC
    cle
    wbr
    #
    cD
    cB
    cle
    wbr
    #
    wa
    #
    wph
    @2
    wa
    #
    @3
    @4
    @6
    @1
    cxr
    clt
    cinf
    #
    @0
    cxr
    clt
    cinf
    #
    cA
    cC
    cle
    @6
    @2
    @1
    cxr
    wss
    #
    @7
    @8
    cle
    wbr
    wph
    @2
    simpr
    #
    vx
    vy
    vz
    cA
    cB
    clt
    clt
    cioo
    vx
    vy
    vz
    df-ioo
    #
    ixxssxr
    #
    @0
    @1
    infxrss
    sylancl
    @6
    cA
    cxr
    wcel
    #
    cB
    cxr
    wcel
    #
    @1
    c0
    wne
    #
    @7
    cA
    wceq
    wph
    @13
    @2
    ioossioobi.a
    adantr
    #
    wph
    @14
    @2
    ioossioobi.b
    adantr
    #
    @6
    @2
    @0
    c0
    wne
    #
    @15
    @10
    wph
    @18
    @2
    wph
    @18
    cC
    cD
    clt
    wbr
    #
    ioossioobi.cltd
    wph
    cC
    cxr
    wcel
    #
    cD
    cxr
    wcel
    #
    @18
    @19
    wb
    ioossioobi.c
    ioossioobi.d
    cC
    cD
    ioon0
    syl2anc
    mpbird
    adantr
    #
    @0
    @1
    ssn0
    syl2anc
    #
    vx
    vy
    vz
    vw
    cA
    cB
    clt
    clt
    cioo
    @11
    vw
    cv
    #
    cxr
    wcel
    #
    @14
    wa
    @24
    cB
    clt
    wbr
    idd
    #
    @24
    cB
    xrltle
    #
    @13
    @25
    wa
    cA
    @24
    clt
    wbr
    idd
    #
    cA
    @24
    xrltle
    #
    ixxlb
    syl3anc
    @6
    @20
    @21
    @18
    @8
    cC
    wceq
    wph
    @20
    @2
    ioossioobi.c
    adantr
    #
    wph
    @21
    @2
    ioossioobi.d
    adantr
    #
    @22
    vx
    vy
    vz
    vw
    cC
    cD
    clt
    clt
    cioo
    @11
    @25
    @21
    wa
    @24
    cD
    clt
    wbr
    idd
    #
    @24
    cD
    xrltle
    #
    @20
    @25
    wa
    cC
    @24
    clt
    wbr
    idd
    #
    cC
    @24
    xrltle
    #
    ixxlb
    syl3anc
    3brtr3d
    @6
    @0
    cxr
    clt
    csup
    #
    @1
    cxr
    clt
    csup
    #
    cD
    cB
    cle
    @6
    @2
    @9
    @36
    @37
    cle
    wbr
    @10
    @12
    @0
    @1
    supxrss
    sylancl
    @6
    @20
    @21
    @18
    @36
    cD
    wceq
    @30
    @31
    @22
    vx
    vy
    vz
    vw
    cC
    cD
    clt
    clt
    cioo
    @11
    @32
    @33
    @34
    @35
    ixxub
    syl3anc
    @6
    @13
    @14
    @15
    @37
    cB
    wceq
    @16
    @17
    @23
    vx
    vy
    vz
    vw
    cA
    cB
    clt
    clt
    cioo
    @11
    @26
    @27
    @28
    @29
    ixxub
    syl3anc
    3brtr3d
    jca
    wph
    @5
    wa
    @13
    @14
    @3
    @4
    @2
    wph
    @13
    @5
    ioossioobi.a
    adantr
    wph
    @14
    @5
    ioossioobi.b
    adantr
    wph
    @3
    @4
    simprl
    wph
    @3
    @4
    simprr
    cA
    cB
    cC
    cD
    ioossioo
    syl22anc
    impbida
end
