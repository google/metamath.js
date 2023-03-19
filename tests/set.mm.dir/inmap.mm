include "cmap.mm"
include "co.mm"
include "cin.mm"
include "cv.mm"
include "wcel.mm"
include "wral.mm"
include "wss.mm"
include "wa.mm"
include "wf.mm"
include "elinel1.mm"
include "elmapi.mm"
include "syl.mm"
include "elinel2.mm"
include "jca.mm"
include "fin.mm"
include "sylibr.mm"
include "adantl.mm"
include "wb.mm"
include "cvv.mm"
include "inss1.mm"
include "a1i.mm"
include "ssexd.mm"
include "elmapd.mm"
include "adantr.mm"
include "mpbird.mm"
include "ralrimiva.mm"
include "dfss3.mm"
include "mapss.mm"
include "syl2anc.mm"
include "inss2.mm"
include "ssind.mm"
include "eqssd.mm"

theorem inmap
  let wph: wff ph
  let cA: class A
  let cB: class B
  let cC: class C
  let cV: class V
  let cW: class W
  let cZ: class Z
  let vf: setvar f
  assume inmap.a: |- ( ph -> A e. V )
  assume inmap.b: |- ( ph -> B e. W )
  assume inmap.c: |- ( ph -> C e. Z )


  assert |- ( ph -> ( ( A ^m C ) i^i ( B ^m C ) ) = ( ( A i^i B ) ^m C ) )

  proof
    wph
    cA
    cC
    cmap
    co
    #
    cB
    cC
    cmap
    co
    #
    cin
    #
    cA
    cB
    cin
    #
    cC
    cmap
    co
    #
    wph
    vf
    cv
    #
    @4
    wcel
    #
    vf
    @2
    wral
    @2
    @4
    wss
    wph
    @6
    vf
    @2
    wph
    @5
    @2
    wcel
    #
    wa
    @6
    cC
    @3
    @5
    wf
    #
    @7
    @8
    wph
    @7
    cC
    cA
    @5
    wf
    #
    cC
    cB
    @5
    wf
    #
    wa
    @8
    @7
    @9
    @10
    @7
    @5
    @0
    wcel
    @9
    @5
    @0
    @1
    elinel1
    @5
    cA
    cC
    elmapi
    syl
    @7
    @5
    @1
    wcel
    @10
    @5
    @0
    @1
    elinel2
    @5
    cB
    cC
    elmapi
    syl
    jca
    cC
    cA
    cB
    @5
    fin
    sylibr
    adantl
    wph
    @6
    @8
    wb
    @7
    wph
    @3
    cC
    @5
    cvv
    cZ
    wph
    @3
    cA
    cV
    inmap.a
    @3
    cA
    wss
    #
    wph
    cA
    cB
    inss1
    a1i
    #
    ssexd
    inmap.c
    elmapd
    adantr
    mpbird
    ralrimiva
    vf
    @2
    @4
    dfss3
    sylibr
    wph
    @4
    @0
    @1
    wph
    cA
    cV
    wcel
    @11
    @4
    @0
    wss
    inmap.a
    @12
    @3
    cA
    cC
    cV
    mapss
    syl2anc
    wph
    cB
    cW
    wcel
    @3
    cB
    wss
    #
    @4
    @1
    wss
    inmap.b
    @13
    wph
    cA
    cB
    inss2
    a1i
    @3
    cB
    cC
    cW
    mapss
    syl2anc
    ssind
    eqssd
end
