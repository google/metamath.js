include "cr.mm"
include "wcel.mm"
include "cle.mm"
include "wbr.mm"
include "w3a.mm"
include "cv.mm"
include "cpnf.mm"
include "cico.mm"
include "co.mm"
include "cima.mm"
include "cxr.mm"
include "cin.mm"
include "clt.mm"
include "csup.mm"
include "wral.mm"
include "wss.mm"
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
include "inss2.mm"
include "supxrcl.mm"
include "ax-mp.mm"
include "xrleid.mm"
include "wb.mm"
include "supxrleub.mm"
include "mp2an.mm"
include "mpbi.mm"
include "ssralv.mm"
include "mpisyl.mm"
include "sylibr.mm"

theorem limsupgord
  let cA: class A
  let cB: class B
  let cF: class F
  let vk: setvar k
  let vx: setvar x
  let vw: setvar w
  let vy: setvar y
  let vz: setvar z


  assert |- ( ( A e. RR /\ B e. RR /\ A <_ B ) -> sup ( ( ( F " ( B [,) +oo ) ) i^i RR* ) , RR* , < ) <_ sup ( ( ( F " ( A [,) +oo ) ) i^i RR* ) , RR* , < ) )

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
    vx
    cv
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
    csup
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
    @11
    cxr
    clt
    csup
    @7
    cle
    wbr
    #
    @3
    @11
    @6
    wss
    #
    @8
    vx
    @6
    wral
    #
    @12
    @3
    @9
    @4
    wss
    #
    @10
    @5
    wss
    @14
    @3
    cA
    cxr
    wcel
    #
    @2
    @16
    @0
    @1
    @17
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
    @18
    cA
    cB
    vw
    cv
    xrletr
    ixxss1
    syl2anc
    @9
    @4
    cF
    imass2
    @10
    @5
    cxr
    ssrin
    3syl
    @7
    @7
    cle
    wbr
    #
    @15
    @7
    cxr
    wcel
    #
    @19
    @6
    cxr
    wss
    #
    @20
    @5
    cxr
    inss2
    #
    @6
    supxrcl
    ax-mp
    #
    @7
    xrleid
    ax-mp
    @21
    @20
    @19
    @15
    wb
    @22
    @23
    vx
    @6
    @7
    supxrleub
    mp2an
    mpbi
    @8
    vx
    @11
    @6
    ssralv
    mpisyl
    @11
    cxr
    wss
    @20
    @13
    @12
    wb
    @10
    cxr
    inss2
    @23
    vx
    @11
    @7
    supxrleub
    mp2an
    sylibr
end
