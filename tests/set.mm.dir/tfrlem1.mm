include "wss.mm"
include "cv.mm"
include "cfv.mm"
include "wceq.mm"
include "wral.mm"
include "ssid.mm"
include "con0.mm"
include "wcel.mm"
include "wi.mm"
include "sseq1.mm"
include "raleq.mm"
include "imbi12d.mm"
include "imbi2d.mm"
include "r19.21v.mm"
include "wa.mm"
include "cres.mm"
include "cdm.mm"
include "wfn.mm"
include "wfun.mm"
include "ad4antr.mm"
include "simpld.mm"
include "funfn.mm"
include "sylib.mm"
include "word.mm"
include "eloni.mm"
include "ad3antlr.mm"
include "ordelss.mm"
include "sylan.mm"
include "simplr.mm"
include "sstrd.mm"
include "simprd.mm"
include "fnssres.mm"
include "syl2anc.mm"
include "simpr.mm"
include "simp-4r.mm"
include "adantr.mm"
include "rspcv.mm"
include "syl3c.mm"
include "fveq2.mm"
include "eqeq12d.mm"
include "sylc.mm"
include "fvres.mm"
include "adantl.mm"
include "3eqtr4d.mm"
include "eqfnfvd.mm"
include "fveq2d.mm"
include "sselda.mm"
include "reseq2.mm"
include "rspcva.mm"
include "ralrimiva.mm"
include "cbvralv.mm"
include "sylibr.mm"
include "exp31.mm"
include "expcom.mm"
include "a2d.mm"
include "syl5bi.mm"
include "tfis3.mm"
include "mpcom.mm"
include "mpi.mm"

theorem tfrlem1
  let wph: wff ph
  let vx: setvar x
  let cA: class A
  let cB: class B
  let cF: class F
  let cG: class G
  let vu: setvar u
  let vw: setvar w
  let vy: setvar y
  let vz: setvar z
  assume tfrlem1.1: |- ( ph -> A e. On )
  assume tfrlem1.2: |- ( ph -> ( Fun F /\ A C_ dom F ) )
  assume tfrlem1.3: |- ( ph -> ( Fun G /\ A C_ dom G ) )
  assume tfrlem1.4: |- ( ph -> A. x e. A ( F ` x ) = ( B ` ( F |` x ) ) )
  assume tfrlem1.5: |- ( ph -> A. x e. A ( G ` x ) = ( B ` ( G |` x ) ) )

  disjoint A x
  disjoint B x
  disjoint F x
  disjoint G x
  disjoint A u
  disjoint A w
  disjoint A y
  disjoint A z
  disjoint u w
  disjoint u x
  disjoint u y
  disjoint u z
  disjoint w x
  disjoint w y
  disjoint w z
  disjoint x y
  disjoint x z
  disjoint y z
  disjoint F u
  disjoint F w
  disjoint F y
  disjoint F z
  disjoint G u
  disjoint G w
  disjoint G y
  disjoint G z
  disjoint ph u
  disjoint ph w
  disjoint ph y
  disjoint ph z
  assert |- ( ph -> A. x e. A ( F ` x ) = ( G ` x ) )

  proof
    wph
    cA
    cA
    wss
    #
    vx
    cv
    #
    cF
    cfv
    #
    @1
    cG
    cfv
    #
    wceq
    #
    vx
    cA
    wral
    #
    cA
    ssid
    cA
    con0
    wcel
    wph
    @0
    @5
    wi
    #
    tfrlem1.1
    wph
    vy
    cv
    #
    cA
    wss
    #
    @4
    vx
    @7
    wral
    #
    wi
    #
    wi
    #
    wph
    vz
    cv
    #
    cA
    wss
    #
    @4
    vx
    @12
    wral
    #
    wi
    #
    wi
    #
    wph
    @6
    wi
    vy
    vz
    cA
    @7
    @12
    wceq
    #
    @10
    @15
    wph
    @17
    @8
    @13
    @9
    @14
    @7
    @12
    cA
    sseq1
    @4
    vx
    @7
    @12
    raleq
    imbi12d
    imbi2d
    @7
    cA
    wceq
    #
    @10
    @6
    wph
    @18
    @8
    @0
    @9
    @5
    @7
    cA
    cA
    sseq1
    @4
    vx
    @7
    cA
    raleq
    imbi12d
    imbi2d
    @16
    vz
    @7
    wral
    wph
    @15
    vz
    @7
    wral
    #
    wi
    @7
    con0
    wcel
    #
    @11
    wph
    @15
    vz
    @7
    r19.21v
    @20
    wph
    @19
    @10
    wph
    @20
    @19
    @10
    wi
    wph
    @20
    wa
    #
    @19
    @8
    @9
    @21
    @19
    wa
    #
    @8
    wa
    #
    vw
    cv
    #
    cF
    cfv
    #
    @24
    cG
    cfv
    #
    wceq
    #
    vw
    @7
    wral
    @9
    @23
    @27
    vw
    @7
    @23
    @24
    @7
    wcel
    #
    wa
    #
    cF
    @24
    cres
    #
    cB
    cfv
    #
    cG
    @24
    cres
    #
    cB
    cfv
    #
    @25
    @26
    @29
    @30
    @32
    cB
    @29
    vu
    @24
    @30
    @32
    @29
    cF
    cF
    cdm
    #
    wfn
    #
    @24
    @34
    wss
    @30
    @24
    wfn
    @29
    cF
    wfun
    #
    @35
    @29
    @36
    cA
    @34
    wss
    #
    wph
    @36
    @37
    wa
    @20
    @19
    @8
    @28
    tfrlem1.2
    ad4antr
    #
    simpld
    cF
    funfn
    sylib
    @29
    @24
    cA
    @34
    @29
    @24
    @7
    cA
    @23
    @7
    word
    #
    @28
    @24
    @7
    wss
    @20
    @39
    wph
    @19
    @8
    @7
    eloni
    ad3antlr
    @7
    @24
    ordelss
    sylan
    @22
    @8
    @28
    simplr
    sstrd
    #
    @29
    @36
    @37
    @38
    simprd
    sstrd
    @34
    @24
    cF
    fnssres
    syl2anc
    @29
    cG
    cG
    cdm
    #
    wfn
    #
    @24
    @41
    wss
    @32
    @24
    wfn
    @29
    cG
    wfun
    #
    @42
    @29
    @43
    cA
    @41
    wss
    #
    wph
    @43
    @44
    wa
    @20
    @19
    @8
    @28
    tfrlem1.3
    ad4antr
    #
    simpld
    cG
    funfn
    sylib
    @29
    @24
    cA
    @41
    @40
    @29
    @43
    @44
    @45
    simprd
    sstrd
    @41
    @24
    cG
    fnssres
    syl2anc
    @29
    vu
    cv
    #
    @24
    wcel
    #
    wa
    #
    @46
    cF
    cfv
    #
    @46
    cG
    cfv
    #
    @46
    @30
    cfv
    #
    @46
    @32
    cfv
    #
    @48
    @47
    @4
    vx
    @24
    wral
    #
    @49
    @50
    wceq
    #
    @29
    @47
    simpr
    @48
    @28
    @19
    @24
    cA
    wss
    #
    @53
    @23
    @28
    @47
    simplr
    @21
    @19
    @8
    @28
    @47
    simp-4r
    @29
    @55
    @47
    @40
    adantr
    @15
    @55
    @53
    wi
    vz
    @24
    @7
    @12
    @24
    wceq
    @13
    @55
    @14
    @53
    @12
    @24
    cA
    sseq1
    @4
    vx
    @12
    @24
    raleq
    imbi12d
    rspcv
    syl3c
    @4
    @54
    vx
    @46
    @24
    @1
    @46
    wceq
    @2
    @49
    @3
    @50
    @1
    @46
    cF
    fveq2
    @1
    @46
    cG
    fveq2
    eqeq12d
    rspcv
    sylc
    @47
    @51
    @49
    wceq
    @29
    @46
    @24
    cF
    fvres
    adantl
    @47
    @52
    @50
    wceq
    @29
    @46
    @24
    cG
    fvres
    adantl
    3eqtr4d
    eqfnfvd
    fveq2d
    @29
    @24
    cA
    wcel
    #
    @2
    cF
    @1
    cres
    #
    cB
    cfv
    #
    wceq
    #
    vx
    cA
    wral
    #
    @25
    @31
    wceq
    #
    @23
    @7
    cA
    @24
    @22
    @8
    simpr
    sselda
    #
    wph
    @60
    @20
    @19
    @8
    @28
    tfrlem1.4
    ad4antr
    @59
    @61
    vx
    @24
    cA
    @1
    @24
    wceq
    #
    @2
    @25
    @58
    @31
    @1
    @24
    cF
    fveq2
    #
    @63
    @57
    @30
    cB
    @1
    @24
    cF
    reseq2
    fveq2d
    eqeq12d
    rspcva
    syl2anc
    @29
    @56
    @3
    cG
    @1
    cres
    #
    cB
    cfv
    #
    wceq
    #
    vx
    cA
    wral
    #
    @26
    @33
    wceq
    #
    @62
    wph
    @68
    @20
    @19
    @8
    @28
    tfrlem1.5
    ad4antr
    @67
    @69
    vx
    @24
    cA
    @63
    @3
    @26
    @66
    @33
    @1
    @24
    cG
    fveq2
    #
    @63
    @65
    @32
    cB
    @1
    @24
    cG
    reseq2
    fveq2d
    eqeq12d
    rspcva
    syl2anc
    3eqtr4d
    ralrimiva
    @4
    @27
    vx
    vw
    @7
    @63
    @2
    @25
    @3
    @26
    @64
    @70
    eqeq12d
    cbvralv
    sylibr
    exp31
    expcom
    a2d
    syl5bi
    tfis3
    mpcom
    mpi
end
