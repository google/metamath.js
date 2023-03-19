include "cvv.mm"
include "wcel.mm"
include "crab.mm"
include "cmpt.mm"
include "clsp.mm"
include "cfv.mm"
include "cuz.mm"
include "cres.mm"
include "wss.mm"
include "wceq.mm"
include "cv.mm"
include "wral.mm"
include "wa.mm"
include "uzssd2.mm"
include "adantr.mm"
include "simpr.mm"
include "sseldd.mm"
include "elexd.mm"
include "jca.mm"
include "rabid.mm"
include "sylibr.mm"
include "ex.mm"
include "ralrimi.mm"
include "nfcv.mm"
include "nfrab1.mm"
include "dfss3f.mm"
include "resmptf.mm"
include "syl.mm"
include "eqcomd.mm"
include "fveq2d.mm"
include "eluzelz2d.mm"
include "eqid.mm"
include "fvexi.mm"
include "rabexf.mm"
include "mptexf.mm"
include "a1i.mm"
include "cdm.mm"
include "cz.mm"
include "dmmptssf.mm"
include "ssrab2f.mm"
include "uzssz.mm"
include "eqsstri.mm"
include "sstri.mm"
include "limsupresuz2.mm"
include "eqtr2d.mm"
include "eqtr4d.mm"
include "mptssid.mm"
include "fveq2i.mm"
include "3eqtr4d.mm"

theorem limsupequzmpt2
  let wph: wff ph
  let cA: class A
  let cB: class B
  let cC: class C
  let vj: setvar j
  let cK: class K
  let cM: class M
  let cN: class N
  let cV: class V
  assume limsupequzmpt2.j: |- F/ j ph
  assume limsupequzmpt2.o: |- F/_ j A
  assume limsupequzmpt2.p: |- F/_ j B
  assume limsupequzmpt2.a: |- A = ( ZZ>= ` M )
  assume limsupequzmpt2.b: |- B = ( ZZ>= ` N )
  assume limsupequzmpt2.k: |- ( ph -> K e. A )
  assume limsupequzmpt2.e: |- ( ph -> K e. B )
  assume limsupequzmpt2.c: |- ( ( ph /\ j e. ( ZZ>= ` K ) ) -> C e. V )

  disjoint K j
  assert |- ( ph -> ( limsup ` ( j e. A |-> C ) ) = ( limsup ` ( j e. B |-> C ) ) )

  proof
    wph
    vj
    cC
    cvv
    wcel
    #
    vj
    cA
    crab
    #
    cC
    cmpt
    #
    clsp
    cfv
    #
    vj
    @0
    vj
    cB
    crab
    #
    cC
    cmpt
    #
    clsp
    cfv
    #
    vj
    cA
    cC
    cmpt
    #
    clsp
    cfv
    #
    vj
    cB
    cC
    cmpt
    #
    clsp
    cfv
    #
    wph
    @3
    vj
    cK
    cuz
    cfv
    #
    cC
    cmpt
    #
    clsp
    cfv
    #
    @6
    wph
    @13
    @2
    @11
    cres
    #
    clsp
    cfv
    @3
    wph
    @12
    @14
    clsp
    wph
    @14
    @12
    wph
    @11
    @1
    wss
    #
    @14
    @12
    wceq
    wph
    vj
    cv
    #
    @1
    wcel
    #
    vj
    @11
    wral
    @15
    wph
    @17
    vj
    @11
    limsupequzmpt2.j
    wph
    @16
    @11
    wcel
    #
    @17
    wph
    @18
    wa
    #
    @16
    cA
    wcel
    #
    @0
    wa
    @17
    @19
    @20
    @0
    @19
    @11
    cA
    @16
    wph
    @11
    cA
    wss
    @18
    wph
    cM
    cK
    cA
    limsupequzmpt2.a
    limsupequzmpt2.k
    uzssd2
    adantr
    wph
    @18
    simpr
    #
    sseldd
    @19
    cC
    cV
    limsupequzmpt2.c
    elexd
    #
    jca
    @0
    vj
    cA
    rabid
    sylibr
    ex
    ralrimi
    vj
    @11
    @1
    vj
    @11
    nfcv
    #
    @0
    vj
    cA
    nfrab1
    #
    dfss3f
    sylibr
    vj
    @1
    @11
    cC
    @24
    @23
    resmptf
    syl
    eqcomd
    fveq2d
    wph
    @2
    cK
    cvv
    @11
    wph
    cM
    cK
    cA
    limsupequzmpt2.a
    limsupequzmpt2.k
    eluzelz2d
    #
    @11
    eqid
    #
    @2
    cvv
    wcel
    wph
    vj
    @1
    cC
    @24
    @0
    vj
    cA
    cvv
    limsupequzmpt2.o
    cA
    cM
    cuz
    limsupequzmpt2.a
    fvexi
    rabexf
    mptexf
    a1i
    @2
    cdm
    #
    cz
    wss
    wph
    @27
    @1
    cz
    vj
    @1
    cC
    @2
    @24
    @2
    eqid
    dmmptssf
    @1
    cA
    cz
    @0
    vj
    cA
    limsupequzmpt2.o
    ssrab2f
    cA
    cM
    cuz
    cfv
    cz
    limsupequzmpt2.a
    cM
    uzssz
    eqsstri
    sstri
    sstri
    a1i
    limsupresuz2
    eqtr2d
    wph
    @13
    @5
    @11
    cres
    #
    clsp
    cfv
    @6
    wph
    @12
    @28
    clsp
    wph
    @28
    @12
    wph
    @11
    @4
    wss
    #
    @28
    @12
    wceq
    wph
    @16
    @4
    wcel
    #
    vj
    @11
    wral
    @29
    wph
    @30
    vj
    @11
    limsupequzmpt2.j
    wph
    @18
    @30
    @19
    @16
    cB
    wcel
    #
    @0
    wa
    @30
    @19
    @31
    @0
    @19
    @11
    cB
    @16
    wph
    @11
    cB
    wss
    @18
    wph
    cN
    cK
    cB
    limsupequzmpt2.b
    limsupequzmpt2.e
    uzssd2
    adantr
    @21
    sseldd
    @22
    jca
    @0
    vj
    cB
    rabid
    sylibr
    ex
    ralrimi
    vj
    @11
    @4
    @23
    @0
    vj
    cB
    nfrab1
    #
    dfss3f
    sylibr
    vj
    @4
    @11
    cC
    @32
    @23
    resmptf
    syl
    eqcomd
    fveq2d
    wph
    @5
    cK
    cvv
    @11
    @25
    @26
    @5
    cvv
    wcel
    wph
    vj
    @4
    cC
    @32
    @0
    vj
    cB
    cvv
    limsupequzmpt2.p
    cB
    cN
    cuz
    limsupequzmpt2.b
    fvexi
    rabexf
    mptexf
    a1i
    @5
    cdm
    #
    cz
    wss
    wph
    @33
    @4
    cz
    vj
    @4
    cC
    @5
    @32
    @5
    eqid
    dmmptssf
    @4
    cB
    cz
    @0
    vj
    cB
    limsupequzmpt2.p
    ssrab2f
    cB
    cN
    cuz
    cfv
    cz
    limsupequzmpt2.b
    cN
    uzssz
    eqsstri
    sstri
    sstri
    a1i
    limsupresuz2
    eqtr2d
    eqtr4d
    @8
    @3
    wceq
    wph
    @7
    @2
    clsp
    vj
    cA
    cC
    @1
    limsupequzmpt2.o
    @1
    eqid
    mptssid
    fveq2i
    a1i
    @10
    @6
    wceq
    wph
    @9
    @5
    clsp
    vj
    cB
    cC
    @4
    limsupequzmpt2.p
    @4
    eqid
    mptssid
    fveq2i
    a1i
    3eqtr4d
end
