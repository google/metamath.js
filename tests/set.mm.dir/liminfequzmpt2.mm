include "cvv.mm"
include "wcel.mm"
include "crab.mm"
include "cmpt.mm"
include "clsi.mm"
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
include "liminfresuz2.mm"
include "eqtr2d.mm"
include "eqtr4d.mm"
include "mptssid.mm"
include "fveq2i.mm"
include "3eqtr4d.mm"

theorem liminfequzmpt2
  let wph: wff ph
  let cA: class A
  let cB: class B
  let cC: class C
  let vj: setvar j
  let cK: class K
  let cM: class M
  let cN: class N
  let cV: class V
  let vk: setvar k
  let vx: setvar x
  assume liminfequzmpt2.j: |- F/ j ph
  assume liminfequzmpt2.o: |- F/_ j A
  assume liminfequzmpt2.p: |- F/_ j B
  assume liminfequzmpt2.a: |- A = ( ZZ>= ` M )
  assume liminfequzmpt2.b: |- B = ( ZZ>= ` N )
  assume liminfequzmpt2.k: |- ( ph -> K e. A )
  assume liminfequzmpt2.e: |- ( ph -> K e. B )
  assume liminfequzmpt2.c: |- ( ( ph /\ j e. ( ZZ>= ` K ) ) -> C e. V )

  disjoint K j
  disjoint k x
  assert |- ( ph -> ( liminf ` ( j e. A |-> C ) ) = ( liminf ` ( j e. B |-> C ) ) )

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
    clsi
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
    clsi
    cfv
    #
    vj
    cA
    cC
    cmpt
    #
    clsi
    cfv
    #
    vj
    cB
    cC
    cmpt
    #
    clsi
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
    clsi
    cfv
    #
    @6
    wph
    @13
    @2
    @11
    cres
    #
    clsi
    cfv
    @3
    wph
    @12
    @14
    clsi
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
    liminfequzmpt2.j
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
    liminfequzmpt2.a
    liminfequzmpt2.k
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
    liminfequzmpt2.c
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
    liminfequzmpt2.a
    liminfequzmpt2.k
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
    liminfequzmpt2.o
    cA
    cM
    cuz
    liminfequzmpt2.a
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
    liminfequzmpt2.o
    ssrab2f
    cA
    cM
    cuz
    cfv
    cz
    liminfequzmpt2.a
    cM
    uzssz
    eqsstri
    sstri
    sstri
    a1i
    liminfresuz2
    eqtr2d
    wph
    @13
    @5
    @11
    cres
    #
    clsi
    cfv
    @6
    wph
    @12
    @28
    clsi
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
    liminfequzmpt2.j
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
    liminfequzmpt2.b
    liminfequzmpt2.e
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
    liminfequzmpt2.p
    cB
    cN
    cuz
    liminfequzmpt2.b
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
    liminfequzmpt2.p
    ssrab2f
    cB
    cN
    cuz
    cfv
    cz
    liminfequzmpt2.b
    cN
    uzssz
    eqsstri
    sstri
    sstri
    a1i
    liminfresuz2
    eqtr2d
    eqtr4d
    @8
    @3
    wceq
    wph
    @7
    @2
    clsi
    vj
    cA
    cC
    @1
    liminfequzmpt2.o
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
    clsi
    vj
    cB
    cC
    @4
    liminfequzmpt2.p
    @4
    eqid
    mptssid
    fveq2i
    a1i
    3eqtr4d
end
