include "cdm.mm"
include "cuni.mm"
include "csuc.mm"
include "cfv.mm"
include "com.mm"
include "coe.mm"
include "co.mm"
include "comu.mm"
include "wf1o.mm"
include "con0.mm"
include "c0.mm"
include "csupp.mm"
include "cvv.mm"
include "wcel.mm"
include "ovex.mm"
include "cep.mm"
include "oion.mm"
include "ax-mp.mm"
include "elexi.mm"
include "uniex.mm"
include "sucid.mm"
include "cnfcom2lem.mm"
include "syl5eleqr.mm"
include "cnfcom.mm"
include "wceq.mm"
include "wb.mm"
include "oveq2i.mm"
include "fveq2i.mm"
include "oveq12i.mm"
include "f1oeq3.mm"
include "sylibr.mm"
include "fveq2d.mm"
include "f1oeq1.mm"
include "syl.mm"
include "mpbird.mm"
include "ccnf.mm"
include "ccnv.mm"
include "omelon.mm"
include "a1i.mm"
include "wf.mm"
include "cantnff1o.mm"
include "f1ocnv.mm"
include "f1of.mm"
include "3syl.mm"
include "ffvelrnd.mm"
include "syl5eqel.mm"
include "cv.mm"
include "coa.mm"
include "cmpt2.mm"
include "cseqom.mm"
include "wa.mm"
include "oveq1i.mm"
include "mpt2eq3ia.mm"
include "eqid.mm"
include "seqomeq12.mm"
include "mp2an.mm"
include "eqtri.mm"
include "cantnfval.mm"
include "syl5reqr.mm"
include "f1ocnvfv2.mm"
include "syl2anc.mm"
include "3eqtr3d.mm"
include "f1oeq2.mm"
include "mpbid.mm"

theorem cnfcom2
  let wph: wff ph
  let vx: setvar x
  let vz: setvar z
  let cA: class A
  let cB: class B
  let cS: class S
  let cT: class T
  let vf: setvar f
  let vk: setvar k
  let cF: class F
  let cG: class G
  let cH: class H
  let cK: class K
  let cM: class M
  let cW: class W
  let vu: setvar u
  let vv: setvar v
  let vw: setvar w
  let vy: setvar y
  let cI: class I
  assume cnfcom.s: |- S = dom ( _om CNF A )
  assume cnfcom.a: |- ( ph -> A e. On )
  assume cnfcom.b: |- ( ph -> B e. ( _om ^o A ) )
  assume cnfcom.f: |- F = ( `' ( _om CNF A ) ` B )
  assume cnfcom.g: |- G = OrdIso ( _E , ( F supp (/) ) )
  assume cnfcom.h: |- H = seqom ( ( k e. _V , z e. _V |-> ( M +o z ) ) , (/) )
  assume cnfcom.t: |- T = seqom ( ( k e. _V , f e. _V |-> K ) , (/) )
  assume cnfcom.m: |- M = ( ( _om ^o ( G ` k ) ) .o ( F ` ( G ` k ) ) )
  assume cnfcom.k: |- K = ( ( x e. M |-> ( dom f +o x ) ) u. `' ( x e. dom f |-> ( M +o x ) ) )
  assume cnfcom.w: |- W = ( G ` U. dom G )
  assume cnfcom2.1: |- ( ph -> (/) e. B )

  disjoint k x
  disjoint k z
  disjoint A k
  disjoint x z
  disjoint A x
  disjoint A z
  disjoint M x
  disjoint f k
  disjoint f x
  disjoint f z
  disjoint F f
  disjoint F k
  disjoint F x
  disjoint F z
  disjoint T z
  disjoint W x
  disjoint G f
  disjoint G k
  disjoint G x
  disjoint G z
  disjoint H f
  disjoint H x
  disjoint S k
  disjoint S z
  disjoint k ph
  disjoint ph x
  disjoint ph z
  disjoint k u
  disjoint k v
  disjoint k w
  disjoint k y
  disjoint I k
  disjoint u v
  disjoint u w
  disjoint u x
  disjoint u y
  disjoint u z
  disjoint I u
  disjoint v w
  disjoint v x
  disjoint v y
  disjoint v z
  disjoint I v
  disjoint w x
  disjoint w y
  disjoint w z
  disjoint I w
  disjoint x y
  disjoint I x
  disjoint y z
  disjoint I y
  disjoint I z
  disjoint M y
  disjoint ph u
  disjoint ph v
  disjoint ph w
  disjoint ph y
  disjoint f u
  disjoint f v
  disjoint f w
  disjoint f y
  disjoint F u
  disjoint F v
  disjoint F w
  disjoint F y
  disjoint K u
  disjoint K v
  disjoint K w
  disjoint T u
  disjoint T v
  disjoint T w
  disjoint T y
  disjoint W u
  disjoint W v
  disjoint G u
  disjoint G v
  disjoint G w
  disjoint G y
  disjoint H u
  disjoint H v
  disjoint H w
  disjoint H y
  assert |- ( ph -> ( T ` dom G ) : B -1-1-onto-> ( ( _om ^o W ) .o ( F ` W ) ) )

  proof
    wph
    cG
    cdm
    #
    cuni
    #
    csuc
    #
    cH
    cfv
    #
    com
    cW
    coe
    co
    #
    cW
    cF
    cfv
    #
    comu
    co
    #
    @0
    cT
    cfv
    #
    wf1o
    #
    cB
    @6
    @7
    wf1o
    #
    wph
    @8
    @3
    @6
    @2
    cT
    cfv
    #
    wf1o
    #
    wph
    @3
    com
    @1
    cG
    cfv
    #
    coe
    co
    #
    @12
    cF
    cfv
    #
    comu
    co
    #
    @10
    wf1o
    #
    @11
    wph
    vx
    vz
    cA
    cB
    cS
    cT
    vf
    vk
    cF
    cG
    cH
    @1
    cK
    cM
    cnfcom.s
    cnfcom.a
    cnfcom.b
    cnfcom.f
    cnfcom.g
    cnfcom.h
    cnfcom.t
    cnfcom.m
    cnfcom.k
    wph
    @1
    @2
    @0
    @1
    @0
    @0
    con0
    cF
    c0
    csupp
    co
    #
    cvv
    wcel
    @0
    con0
    wcel
    cF
    c0
    csupp
    ovex
    @17
    cep
    cG
    cvv
    cnfcom.g
    oion
    ax-mp
    elexi
    uniex
    sucid
    wph
    vx
    vz
    cA
    cB
    cS
    cT
    vf
    vk
    cF
    cG
    cH
    cK
    cM
    cW
    cnfcom.s
    cnfcom.a
    cnfcom.b
    cnfcom.f
    cnfcom.g
    cnfcom.h
    cnfcom.t
    cnfcom.m
    cnfcom.k
    cnfcom.w
    cnfcom2.1
    cnfcom2lem
    #
    syl5eleqr
    cnfcom
    @6
    @15
    wceq
    @11
    @16
    wb
    @4
    @13
    @5
    @14
    comu
    cW
    @12
    com
    coe
    cnfcom.w
    oveq2i
    cW
    @12
    cF
    cnfcom.w
    fveq2i
    oveq12i
    @6
    @15
    @3
    @10
    f1oeq3
    ax-mp
    sylibr
    wph
    @7
    @10
    wceq
    @8
    @11
    wb
    wph
    @0
    @2
    cT
    @18
    fveq2d
    @3
    @6
    @7
    @10
    f1oeq1
    syl
    mpbird
    wph
    @3
    cB
    wceq
    @8
    @9
    wb
    wph
    @0
    cH
    cfv
    #
    cB
    com
    cA
    ccnf
    co
    #
    ccnv
    #
    cfv
    #
    @20
    cfv
    #
    @3
    cB
    wph
    @23
    cF
    @20
    cfv
    @19
    cF
    @22
    @20
    cnfcom.f
    fveq2i
    wph
    vz
    com
    cA
    cS
    vk
    cF
    cG
    cH
    cnfcom.s
    com
    con0
    wcel
    wph
    omelon
    a1i
    #
    cnfcom.a
    cnfcom.g
    wph
    cF
    @22
    cS
    cnfcom.f
    wph
    com
    cA
    coe
    co
    #
    cS
    cB
    @21
    wph
    cS
    @25
    @20
    wf1o
    #
    @25
    cS
    @21
    wf1o
    @25
    cS
    @21
    wf
    wph
    com
    cA
    cS
    cnfcom.s
    @24
    cnfcom.a
    cantnff1o
    #
    cS
    @25
    @20
    f1ocnv
    @25
    cS
    @21
    f1of
    3syl
    cnfcom.b
    ffvelrnd
    syl5eqel
    cH
    vk
    vz
    cvv
    cvv
    cM
    vz
    cv
    #
    coa
    co
    #
    cmpt2
    #
    c0
    cseqom
    #
    vk
    vz
    cvv
    cvv
    com
    vk
    cv
    #
    cG
    cfv
    #
    coe
    co
    @33
    cF
    cfv
    comu
    co
    #
    @28
    coa
    co
    #
    cmpt2
    #
    c0
    cseqom
    #
    cnfcom.h
    @30
    @36
    wceq
    c0
    c0
    wceq
    @31
    @37
    wceq
    vk
    vz
    cvv
    cvv
    @29
    @35
    @29
    @35
    wceq
    @32
    cvv
    wcel
    @28
    cvv
    wcel
    wa
    cM
    @34
    @28
    coa
    cnfcom.m
    oveq1i
    a1i
    mpt2eq3ia
    c0
    eqid
    @30
    @36
    c0
    c0
    seqomeq12
    mp2an
    eqtri
    cantnfval
    syl5reqr
    wph
    @0
    @2
    cH
    @18
    fveq2d
    wph
    @26
    cB
    @25
    wcel
    @23
    cB
    wceq
    @27
    cnfcom.b
    cS
    @25
    cB
    @20
    f1ocnvfv2
    syl2anc
    3eqtr3d
    @3
    cB
    @6
    @7
    f1oeq2
    syl
    mpbid
end
