include "cicc.mm"
include "co.mm"
include "cdif.mm"
include "cioc.mm"
include "cv.mm"
include "wcel.mm"
include "wral.mm"
include "wss.mm"
include "wa.mm"
include "cxr.mm"
include "adantr.mm"
include "iccssxr.mm"
include "eldifi.mm"
include "sseldi.mm"
include "adantl.mm"
include "clt.mm"
include "wbr.mm"
include "wn.mm"
include "ad2antrr.mm"
include "cle.mm"
include "iccgelb.mm"
include "syl3anc.mm"
include "simpr.mm"
include "wb.mm"
include "xrlenltd.mm"
include "mpbird.mm"
include "eliccxrd.mm"
include "eldifn.mm"
include "ad2antlr.mm"
include "condan.mm"
include "iccleub.mm"
include "eliocd.mm"
include "ralrimiva.mm"
include "dfss3.mm"
include "sylibr.mm"
include "iocssxr.mm"
include "id.mm"
include "iocgtlb.mm"
include "xrlelttrd.mm"
include "xrltled.mm"
include "iocleub.mm"
include "xrgtnelicc.mm"
include "eldifd.mm"
include "eqssd.mm"

theorem iccdificc
  let wph: wff ph
  let cA: class A
  let cB: class B
  let cC: class C
  let vx: setvar x
  assume iccdificc.a: |- ( ph -> A e. RR* )
  assume iccdificc.b: |- ( ph -> B e. RR* )
  assume iccdificc.c: |- ( ph -> C e. RR* )
  assume iccdificc.4: |- ( ph -> A <_ B )


  assert |- ( ph -> ( ( A [,] C ) \ ( A [,] B ) ) = ( B (,] C ) )

  proof
    wph
    cA
    cC
    cicc
    co
    #
    cA
    cB
    cicc
    co
    #
    cdif
    #
    cB
    cC
    cioc
    co
    #
    wph
    vx
    cv
    #
    @3
    wcel
    #
    vx
    @2
    wral
    @2
    @3
    wss
    wph
    @5
    vx
    @2
    wph
    @4
    @2
    wcel
    #
    wa
    #
    cB
    cC
    @4
    wph
    cB
    cxr
    wcel
    #
    @6
    iccdificc.b
    adantr
    #
    wph
    cC
    cxr
    wcel
    #
    @6
    iccdificc.c
    adantr
    #
    @6
    @4
    cxr
    wcel
    #
    wph
    @6
    @0
    cxr
    @4
    cA
    cC
    iccssxr
    @4
    @0
    @1
    eldifi
    #
    sseldi
    adantl
    #
    @7
    cB
    @4
    clt
    wbr
    #
    @4
    @1
    wcel
    #
    @7
    @15
    wn
    #
    wa
    #
    cA
    cB
    @4
    wph
    cA
    cxr
    wcel
    #
    @6
    @17
    iccdificc.a
    ad2antrr
    @7
    @8
    @17
    @9
    adantr
    @7
    @12
    @17
    @14
    adantr
    @7
    cA
    @4
    cle
    wbr
    #
    @17
    @7
    @19
    @10
    @4
    @0
    wcel
    #
    @20
    wph
    @19
    @6
    iccdificc.a
    adantr
    #
    @11
    @6
    @21
    wph
    @13
    adantl
    #
    cA
    cC
    @4
    iccgelb
    syl3anc
    adantr
    @18
    @4
    cB
    cle
    wbr
    #
    @17
    @7
    @17
    simpr
    @7
    @24
    @17
    wb
    @17
    @7
    @4
    cB
    @14
    @9
    xrlenltd
    adantr
    mpbird
    eliccxrd
    @6
    @16
    wn
    wph
    @17
    @4
    @0
    @1
    eldifn
    ad2antlr
    condan
    @7
    @19
    @10
    @21
    @4
    cC
    cle
    wbr
    #
    @22
    @11
    @23
    cA
    cC
    @4
    iccleub
    syl3anc
    eliocd
    ralrimiva
    vx
    @2
    @3
    dfss3
    sylibr
    wph
    @6
    vx
    @3
    wral
    @3
    @2
    wss
    wph
    @6
    vx
    @3
    wph
    @5
    wa
    #
    @4
    @0
    @1
    @26
    cA
    cC
    @4
    wph
    @19
    @5
    iccdificc.a
    adantr
    #
    wph
    @10
    @5
    iccdificc.c
    adantr
    #
    @5
    @12
    wph
    @5
    @3
    cxr
    @4
    cB
    cC
    iocssxr
    @5
    id
    sseldi
    adantl
    #
    @26
    cA
    @4
    @27
    @29
    @26
    cA
    cB
    @4
    @27
    wph
    @8
    @5
    iccdificc.b
    adantr
    #
    @29
    wph
    cA
    cB
    cle
    wbr
    @5
    iccdificc.4
    adantr
    @26
    @8
    @10
    @5
    @15
    @30
    @28
    wph
    @5
    simpr
    #
    cB
    cC
    @4
    iocgtlb
    syl3anc
    #
    xrlelttrd
    xrltled
    @26
    @8
    @10
    @5
    @25
    @30
    @28
    @31
    cB
    cC
    @4
    iocleub
    syl3anc
    eliccxrd
    @26
    cA
    cB
    @4
    @27
    @30
    @29
    @32
    xrgtnelicc
    eldifd
    ralrimiva
    vx
    @3
    @2
    dfss3
    sylibr
    eqssd
end
