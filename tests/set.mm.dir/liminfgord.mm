include "cr.mm"
include "wcel.mm"
include "cle.mm"
include "wbr.mm"
include "w3a.mm"
include "cpnf.mm"
include "cico.mm"
include "co.mm"
include "cima.mm"
include "cxr.mm"
include "cin.mm"
include "clt.mm"
include "cinf.mm"
include "cv.mm"
include "wral.mm"
include "wa.mm"
include "wss.mm"
include "inss2.mm"
include "a1i.mm"
include "rexr.mm"
include "3ad2ant1.mm"
include "simp3.mm"
include "df-ico.mm"
include "xrletr.mm"
include "ixxss1.mm"
include "syl2anc.mm"
include "imass2.mm"
include "ssrin.mm"
include "3syl.mm"
include "sselda.mm"
include "infxrlb.mm"
include "ralrimiva.mm"
include "wb.mm"
include "infxrcl.mm"
include "ax-mp.mm"
include "infxrgelb.mm"
include "mp2an.mm"
include "sylibr.mm"

theorem liminfgord
  let cA: class A
  let cB: class B
  let cF: class F
  let vw: setvar w
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let vk: setvar k


  assert |- ( ( A e. RR /\ B e. RR /\ A <_ B ) -> inf ( ( ( F " ( A [,) +oo ) ) i^i RR* ) , RR* , < ) <_ inf ( ( ( F " ( B [,) +oo ) ) i^i RR* ) , RR* , < ) )

  proof
    cA
    cr
    wcel
    #
    cB
    cr
    wcel
    #
    cA
    cB
    cle
    wbr
    #
    w3a
    #
    cF
    cA
    cpnf
    cico
    co
    #
    cima
    #
    cxr
    cin
    #
    cxr
    clt
    cinf
    #
    vx
    cv
    #
    cle
    wbr
    #
    vx
    cF
    cB
    cpnf
    cico
    co
    #
    cima
    #
    cxr
    cin
    #
    wral
    #
    @7
    @12
    cxr
    clt
    cinf
    cle
    wbr
    #
    @3
    @9
    vx
    @12
    @3
    @8
    @12
    wcel
    wa
    #
    @6
    cxr
    wss
    #
    @8
    @6
    wcel
    @9
    @16
    @15
    @5
    cxr
    inss2
    #
    a1i
    @3
    @12
    @6
    @8
    @3
    @10
    @4
    wss
    #
    @11
    @5
    wss
    @12
    @6
    wss
    @3
    cA
    cxr
    wcel
    #
    @2
    @18
    @0
    @1
    @19
    @2
    cA
    rexr
    3ad2ant1
    @0
    @1
    @2
    simp3
    vx
    vy
    vz
    vw
    cA
    cB
    cpnf
    cico
    cle
    clt
    cle
    cico
    cle
    vx
    vy
    vz
    df-ico
    #
    @20
    cA
    cB
    vw
    cv
    xrletr
    ixxss1
    syl2anc
    @10
    @4
    cF
    imass2
    @11
    @5
    cxr
    ssrin
    3syl
    sselda
    @6
    @8
    infxrlb
    syl2anc
    ralrimiva
    @12
    cxr
    wss
    @7
    cxr
    wcel
    #
    @14
    @13
    wb
    @11
    cxr
    inss2
    @16
    @21
    @17
    @6
    infxrcl
    ax-mp
    vx
    @12
    @7
    infxrgelb
    mp2an
    sylibr
end
