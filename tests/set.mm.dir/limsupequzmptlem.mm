include "cmpt.mm"
include "nfmpt1.mm"
include "cuz.mm"
include "cfv.mm"
include "cv.mm"
include "wcel.mm"
include "eqcomi.mm"
include "eleq2i.mm"
include "biimpi.mm"
include "sylan2.mm"
include "mpteq1i.mm"
include "fnmptd.mm"
include "bicomi.mm"
include "cle.mm"
include "wbr.mm"
include "cif.mm"
include "cz.mm"
include "ifcld.mm"
include "syl5eqel.mm"
include "wa.mm"
include "wceq.mm"
include "wss.mm"
include "eqid.mm"
include "cr.mm"
include "zred.mm"
include "max1.mm"
include "syl2anc.mm"
include "syl6breqr.mm"
include "eluzd.mm"
include "uzssd.mm"
include "a1i.mm"
include "sseqtrd.mm"
include "adantr.mm"
include "simpr.mm"
include "sseldd.mm"
include "syldan.mm"
include "fvmpt2.mm"
include "max2.mm"
include "eqtr4d.mm"
include "limsupequz.mm"

theorem limsupequzmptlem
  let wph: wff ph
  let cA: class A
  let cB: class B
  let cC: class C
  let vj: setvar j
  let cK: class K
  let cM: class M
  let cN: class N
  let cV: class V
  let cW: class W
  assume limsupequzmptlem.j: |- F/ j ph
  assume limsupequzmptlem.m: |- ( ph -> M e. ZZ )
  assume limsupequzmptlem.n: |- ( ph -> N e. ZZ )
  assume limsupequzmptlem.a: |- A = ( ZZ>= ` M )
  assume limsupequzmptlem.b: |- B = ( ZZ>= ` N )
  assume limsupequzmptlem.c: |- ( ( ph /\ j e. A ) -> C e. V )
  assume limsupequzmptlem.d: |- ( ( ph /\ j e. B ) -> C e. W )
  assume limsupequzmptlem.k: |- K = if ( M <_ N , N , M )

  disjoint A j
  disjoint B j
  disjoint K j
  disjoint M j
  disjoint N j
  assert |- ( ph -> ( limsup ` ( j e. A |-> C ) ) = ( limsup ` ( j e. B |-> C ) ) )

  proof
    wph
    vj
    vj
    cA
    cC
    cmpt
    #
    vj
    cB
    cC
    cmpt
    #
    cK
    cM
    cN
    limsupequzmptlem.j
    vj
    cA
    cC
    nfmpt1
    vj
    cB
    cC
    nfmpt1
    limsupequzmptlem.m
    wph
    vj
    cM
    cuz
    cfv
    #
    cC
    @0
    cV
    limsupequzmptlem.j
    vj
    cv
    #
    @2
    wcel
    #
    wph
    @3
    cA
    wcel
    #
    cC
    cV
    wcel
    #
    @4
    @5
    @2
    cA
    @3
    cA
    @2
    limsupequzmptlem.a
    eqcomi
    #
    eleq2i
    biimpi
    limsupequzmptlem.c
    sylan2
    vj
    cA
    @2
    cC
    limsupequzmptlem.a
    mpteq1i
    fnmptd
    limsupequzmptlem.n
    wph
    vj
    cN
    cuz
    cfv
    #
    cC
    @1
    cW
    limsupequzmptlem.j
    @3
    @8
    wcel
    #
    wph
    @3
    cB
    wcel
    #
    cC
    cW
    wcel
    @9
    @10
    @10
    @9
    cB
    @8
    @3
    limsupequzmptlem.b
    eleq2i
    bicomi
    biimpi
    limsupequzmptlem.d
    sylan2
    vj
    cB
    @8
    cC
    limsupequzmptlem.b
    mpteq1i
    fnmptd
    wph
    cK
    cM
    cN
    cle
    wbr
    #
    cN
    cM
    cif
    #
    cz
    limsupequzmptlem.k
    wph
    @11
    cN
    cM
    cz
    limsupequzmptlem.n
    limsupequzmptlem.m
    ifcld
    syl5eqel
    #
    wph
    @3
    cK
    cuz
    cfv
    #
    wcel
    #
    wa
    #
    @3
    @0
    cfv
    #
    cC
    @3
    @1
    cfv
    #
    @16
    @5
    @6
    @17
    cC
    wceq
    @16
    @14
    cA
    @3
    wph
    @14
    cA
    wss
    @15
    wph
    @14
    @2
    cA
    wph
    cM
    cK
    wph
    cM
    cK
    @2
    @2
    eqid
    limsupequzmptlem.m
    @13
    wph
    cM
    @12
    cK
    cle
    wph
    cM
    cr
    wcel
    #
    cN
    cr
    wcel
    #
    cM
    @12
    cle
    wbr
    wph
    cM
    limsupequzmptlem.m
    zred
    #
    wph
    cN
    limsupequzmptlem.n
    zred
    #
    cM
    cN
    max1
    syl2anc
    limsupequzmptlem.k
    syl6breqr
    eluzd
    uzssd
    @2
    cA
    wceq
    wph
    @7
    a1i
    sseqtrd
    adantr
    wph
    @15
    simpr
    #
    sseldd
    #
    wph
    @15
    @5
    @6
    @24
    limsupequzmptlem.c
    syldan
    #
    vj
    cA
    cC
    cV
    @0
    @0
    eqid
    fvmpt2
    syl2anc
    @16
    @10
    @6
    @18
    cC
    wceq
    @16
    @14
    cB
    @3
    wph
    @14
    cB
    wss
    @15
    wph
    @14
    @8
    cB
    wph
    cN
    cK
    wph
    cN
    cK
    @8
    @8
    eqid
    limsupequzmptlem.n
    @13
    wph
    cN
    @12
    cK
    cle
    wph
    @19
    @20
    cN
    @12
    cle
    wbr
    @21
    @22
    cM
    cN
    max2
    syl2anc
    limsupequzmptlem.k
    syl6breqr
    eluzd
    uzssd
    @8
    cB
    wceq
    wph
    cB
    @8
    limsupequzmptlem.b
    eqcomi
    a1i
    sseqtrd
    adantr
    @23
    sseldd
    @25
    vj
    cB
    cC
    cV
    @1
    @1
    eqid
    fvmpt2
    syl2anc
    eqtr4d
    limsupequz
end
