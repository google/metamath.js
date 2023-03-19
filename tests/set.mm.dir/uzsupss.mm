include "cz.mm"
include "wcel.mm"
include "wss.mm"
include "cv.mm"
include "cle.mm"
include "wbr.mm"
include "wral.mm"
include "wrex.mm"
include "w3a.mm"
include "clt.mm"
include "wn.mm"
include "wi.mm"
include "wa.mm"
include "c0.mm"
include "wceq.mm"
include "cuz.mm"
include "cfv.mm"
include "simpl1.mm"
include "uzid.mm"
include "syl.mm"
include "syl6eleqr.mm"
include "ral0.mm"
include "simpr.mm"
include "raleqdv.mm"
include "mpbiri.mm"
include "eluzle.mm"
include "wb.mm"
include "eluzel2.mm"
include "eluzelz.mm"
include "cr.mm"
include "zre.mm"
include "lenlt.mm"
include "syl2an.mm"
include "syl2anc.mm"
include "mpbid.mm"
include "eleq2s.mm"
include "pm2.21d.mm"
include "rgen.mm"
include "a1i.mm"
include "breq1.mm"
include "notbid.mm"
include "ralbidv.mm"
include "breq2.mm"
include "imbi1d.mm"
include "anbi12d.mm"
include "rspcev.mm"
include "syl12anc.mm"
include "wne.mm"
include "simpl2.mm"
include "uzssz.mm"
include "eqsstri.mm"
include "syl6ss.mm"
include "simpl3.mm"
include "zsupss.mm"
include "syl3anc.mm"
include "ssrexv.mm"
include "sylc.mm"
include "pm2.61dane.mm"

theorem uzsupss
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let cA: class A
  let cM: class M
  let cZ: class Z
  let vm: setvar m
  let vn: setvar n
  let vw: setvar w
  let cB: class B
  assume uzsupss.1: |- Z = ( ZZ>= ` M )

  disjoint x y
  disjoint x z
  disjoint A x
  disjoint y z
  disjoint A y
  disjoint A z
  disjoint M x
  disjoint M y
  disjoint Z x
  disjoint m n
  disjoint m w
  disjoint m x
  disjoint m y
  disjoint m z
  disjoint A m
  disjoint n w
  disjoint n x
  disjoint n y
  disjoint n z
  disjoint A n
  disjoint w x
  disjoint w y
  disjoint w z
  disjoint A w
  disjoint B n
  disjoint B x
  assert |- ( ( M e. ZZ /\ A C_ Z /\ E. x e. ZZ A. y e. A y <_ x ) -> E. x e. Z ( A. y e. A -. x < y /\ A. y e. Z ( y < x -> E. z e. A y < z ) ) )

  proof
    cM
    cz
    wcel
    #
    cA
    cZ
    wss
    #
    vy
    cv
    #
    vx
    cv
    #
    cle
    wbr
    vy
    cA
    wral
    vx
    cz
    wrex
    #
    w3a
    #
    @3
    @2
    clt
    wbr
    #
    wn
    #
    vy
    cA
    wral
    #
    @2
    @3
    clt
    wbr
    #
    @2
    vz
    cv
    clt
    wbr
    vz
    cA
    wrex
    #
    wi
    #
    vy
    cZ
    wral
    #
    wa
    #
    vx
    cZ
    wrex
    #
    cA
    c0
    @5
    cA
    c0
    wceq
    #
    wa
    #
    cM
    cZ
    wcel
    cM
    @2
    clt
    wbr
    #
    wn
    #
    vy
    cA
    wral
    #
    @2
    cM
    clt
    wbr
    #
    @10
    wi
    #
    vy
    cZ
    wral
    #
    @14
    @16
    cM
    cM
    cuz
    cfv
    #
    cZ
    @16
    @0
    cM
    @23
    wcel
    @0
    @1
    @4
    @15
    simpl1
    cM
    uzid
    syl
    uzsupss.1
    syl6eleqr
    @16
    @19
    @18
    vy
    c0
    wral
    @18
    vy
    ral0
    @16
    @18
    vy
    cA
    c0
    @5
    @15
    simpr
    raleqdv
    mpbiri
    @22
    @16
    @21
    vy
    cZ
    @2
    cZ
    wcel
    @20
    @10
    @20
    wn
    #
    @2
    @23
    cZ
    @2
    @23
    wcel
    #
    cM
    @2
    cle
    wbr
    #
    @24
    cM
    @2
    eluzle
    @25
    @0
    @2
    cz
    wcel
    #
    @26
    @24
    wb
    #
    cM
    @2
    eluzel2
    cM
    @2
    eluzelz
    @0
    cM
    cr
    wcel
    @2
    cr
    wcel
    @28
    @27
    cM
    zre
    @2
    zre
    cM
    @2
    lenlt
    syl2an
    syl2anc
    mpbid
    uzsupss.1
    eleq2s
    pm2.21d
    rgen
    a1i
    @13
    @19
    @22
    wa
    vx
    cM
    cZ
    @3
    cM
    wceq
    #
    @8
    @19
    @12
    @22
    @29
    @7
    @18
    vy
    cA
    @29
    @6
    @17
    @3
    cM
    @2
    clt
    breq1
    notbid
    ralbidv
    @29
    @11
    @21
    vy
    cZ
    @29
    @9
    @20
    @10
    @3
    cM
    @2
    clt
    breq2
    imbi1d
    ralbidv
    anbi12d
    rspcev
    syl12anc
    @5
    cA
    c0
    wne
    #
    wa
    #
    @1
    @13
    vx
    cA
    wrex
    #
    @14
    @0
    @1
    @4
    @30
    simpl2
    #
    @31
    cA
    cz
    wss
    @30
    @4
    @32
    @31
    cA
    cZ
    cz
    @33
    cZ
    @23
    cz
    uzsupss.1
    cM
    uzssz
    eqsstri
    syl6ss
    @5
    @30
    simpr
    @0
    @1
    @4
    @30
    simpl3
    vx
    vy
    vz
    cA
    cZ
    zsupss
    syl3anc
    @13
    vx
    cA
    cZ
    ssrexv
    sylc
    pm2.61dane
end
