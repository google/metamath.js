include "wcel.mm"
include "cv.mm"
include "wsbc.mm"
include "wrex.mm"
include "crab.mm"
include "cvv.mm"
include "wss.mm"
include "wral.mm"
include "w3a.mm"
include "wex.mm"
include "rabexg.mm"
include "ssrab2.mm"
include "a1i.mm"
include "nfv.mm"
include "nfre1.mm"
include "wa.mm"
include "sbceq2a.mm"
include "rspcev.mm"
include "ancoms.mm"
include "anim2i.mm"
include "anasss.mm"
include "wceq.mm"
include "sbcbidv.mm"
include "rexbidv.mm"
include "elrab.mm"
include "sylibr.mm"
include "sylancom.mm"
include "nfcv.mm"
include "nfsbc1v.mm"
include "nfsbc.mm"
include "nfrex.mm"
include "nfrab.mm"
include "cbvrexf.mm"
include "sylib.mm"
include "exp31.mm"
include "rexlimd.mm"
include "ralimia.mm"
include "cbvrex.mm"
include "syl6bb.mm"
include "simprbi.mm"
include "rgen.mm"
include "3jca.mm"
include "sseq1.mm"
include "nfeq2.mm"
include "rexeqf.mm"
include "ralbid.mm"
include "raleqf.mm"
include "3anbi123d.mm"
include "spcegv.mm"
include "imp.mm"
include "syl2an.mm"

theorem indexa
  let wph: wff ph
  let vx: setvar x
  let vy: setvar y
  let cA: class A
  let cB: class B
  let cM: class M
  let vc: setvar c
  let vz: setvar z
  let vw: setvar w
  let vv: setvar v

  disjoint A x
  disjoint A y
  disjoint A c
  disjoint x y
  disjoint c x
  disjoint c y
  disjoint B x
  disjoint B y
  disjoint B c
  disjoint c ph
  disjoint A z
  disjoint A w
  disjoint A v
  disjoint x z
  disjoint w x
  disjoint v x
  disjoint y z
  disjoint w y
  disjoint v y
  disjoint c z
  disjoint c w
  disjoint c v
  disjoint w z
  disjoint v z
  disjoint v w
  disjoint B z
  disjoint B w
  disjoint B v
  disjoint ph z
  disjoint ph w
  disjoint ph v
  assert |- ( ( B e. M /\ A. x e. A E. y e. B ph ) -> E. c ( c C_ B /\ A. x e. A E. y e. c ph /\ A. y e. c E. x e. A ph ) )

  proof
    cB
    cM
    wcel
    wph
    vy
    vz
    cv
    #
    wsbc
    #
    vx
    vw
    cv
    #
    wsbc
    #
    vw
    cA
    wrex
    #
    vz
    cB
    crab
    #
    cvv
    wcel
    #
    @5
    cB
    wss
    #
    wph
    vy
    @5
    wrex
    #
    vx
    cA
    wral
    #
    wph
    vx
    cA
    wrex
    #
    vy
    @5
    wral
    #
    w3a
    #
    vc
    cv
    #
    cB
    wss
    #
    wph
    vy
    @13
    wrex
    #
    vx
    cA
    wral
    #
    @10
    vy
    @13
    wral
    #
    w3a
    #
    vc
    wex
    #
    wph
    vy
    cB
    wrex
    #
    vx
    cA
    wral
    #
    @4
    vz
    cB
    cM
    rabexg
    @21
    @7
    @9
    @11
    @7
    @21
    @4
    vz
    cB
    ssrab2
    a1i
    @20
    @8
    vx
    cA
    vx
    cv
    #
    cA
    wcel
    #
    wph
    @8
    vy
    cB
    @23
    vy
    nfv
    wph
    vy
    @5
    nfre1
    @23
    vy
    cv
    #
    cB
    wcel
    #
    wph
    @8
    @23
    @25
    wa
    #
    wph
    wa
    #
    wph
    vy
    vv
    cv
    #
    wsbc
    #
    vv
    @5
    wrex
    #
    @8
    @26
    wph
    @24
    @5
    wcel
    #
    @30
    @27
    @25
    wph
    vx
    @2
    wsbc
    #
    vw
    cA
    wrex
    #
    wa
    #
    @31
    wph
    @26
    @34
    wph
    @23
    @25
    @34
    @25
    wph
    @23
    wa
    #
    @34
    @35
    @33
    @25
    @23
    wph
    @33
    @32
    wph
    vw
    @22
    cA
    wph
    vx
    @2
    sbceq2a
    #
    rspcev
    ancoms
    anim2i
    ancoms
    anasss
    ancoms
    @4
    @33
    vz
    @24
    cB
    @0
    @24
    wceq
    #
    @3
    @32
    vw
    cA
    @37
    @1
    wph
    vx
    @2
    wph
    vy
    @0
    sbceq2a
    sbcbidv
    rexbidv
    #
    elrab
    sylibr
    @29
    wph
    vv
    @24
    @5
    wph
    vy
    @28
    sbceq2a
    #
    rspcev
    sylancom
    @29
    wph
    vv
    vy
    @5
    vv
    @5
    nfcv
    @4
    vy
    vz
    cB
    @3
    vy
    vw
    cA
    vy
    cA
    nfcv
    @1
    vy
    vx
    @2
    vy
    @2
    nfcv
    wph
    vy
    @0
    nfsbc1v
    nfsbc
    nfrex
    vy
    cB
    nfcv
    nfrab
    #
    wph
    vy
    @28
    nfsbc1v
    wph
    vv
    nfv
    @39
    cbvrexf
    sylib
    exp31
    rexlimd
    ralimia
    @11
    @21
    @10
    vy
    @5
    @31
    @25
    @10
    @4
    @10
    vz
    @24
    cB
    @37
    @4
    @33
    @10
    @38
    @32
    wph
    vw
    vx
    cA
    wph
    vx
    @2
    nfsbc1v
    wph
    vw
    nfv
    @36
    cbvrex
    syl6bb
    elrab
    simprbi
    rgen
    a1i
    3jca
    @6
    @12
    @19
    @18
    @12
    vc
    @5
    cvv
    @13
    @5
    wceq
    #
    @14
    @7
    @16
    @9
    @17
    @11
    @13
    @5
    cB
    sseq1
    @41
    @15
    @8
    vx
    cA
    vx
    @13
    @5
    @4
    vx
    vz
    cB
    @3
    vx
    vw
    cA
    vx
    cA
    nfcv
    @1
    vx
    @2
    nfsbc1v
    nfrex
    vx
    cB
    nfcv
    nfrab
    nfeq2
    wph
    vy
    @13
    @5
    vy
    @13
    nfcv
    #
    @40
    rexeqf
    ralbid
    @10
    vy
    @13
    @5
    @42
    @40
    raleqf
    3anbi123d
    spcegv
    imp
    syl2an
end
