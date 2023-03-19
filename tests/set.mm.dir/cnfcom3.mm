include "com.mm"
include "coe.mm"
include "co.mm"
include "ccnv.mm"
include "ccom.mm"
include "cdm.mm"
include "cfv.mm"
include "wf1o.mm"
include "comu.mm"
include "con0.mm"
include "wcel.mm"
include "omelon.mm"
include "c0.mm"
include "csupp.mm"
include "suppssdm.mm"
include "wf.mm"
include "wceq.mm"
include "cfsupp.mm"
include "wbr.mm"
include "wa.mm"
include "ccnf.mm"
include "a1i.mm"
include "cantnff1o.mm"
include "f1ocnv.mm"
include "f1of.mm"
include "3syl.mm"
include "ffvelrnd.mm"
include "syl5eqel.mm"
include "cantnfs.mm"
include "mpbid.mm"
include "simpld.mm"
include "fdm.mm"
include "syl.mm"
include "syl5sseq.mm"
include "cuni.mm"
include "csuc.mm"
include "cvv.mm"
include "ovex.mm"
include "cep.mm"
include "oion.mm"
include "ax-mp.mm"
include "elexi.mm"
include "uniex.mm"
include "sucid.mm"
include "peano1.mm"
include "sseldd.mm"
include "cnfcom2lem.mm"
include "syl5eleqr.mm"
include "oif.mm"
include "ffvelrni.mm"
include "onelon.mm"
include "syl2anc.mm"
include "oecl.mm"
include "sylancr.mm"
include "nnon.mm"
include "omf1o.mm"
include "wb.mm"
include "wne.mm"
include "wfn.mm"
include "ffn.mm"
include "0ex.mm"
include "elsuppfn.mm"
include "syl3anc.mm"
include "simpr.mm"
include "syl6bi.mm"
include "mpd.mm"
include "on0eln0.mm"
include "mpbird.mm"
include "c1o.mm"
include "cdif.mm"
include "cnfcom3lem.mm"
include "ondif1.mm"
include "simprbi.mm"
include "omabs.mm"
include "syl22anc.mm"
include "f1oeq3.mm"
include "cnfcom2.mm"
include "f1oco.mm"
include "f1oeq1.mm"
include "sylibr.mm"

theorem cnfcom3
  let wph: wff ph
  let vx: setvar x
  let vz: setvar z
  let vv: setvar v
  let vu: setvar u
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
  let cN: class N
  let cW: class W
  let cX: class X
  let cY: class Y
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
  assume cnfcom3.1: |- ( ph -> _om C_ B )
  assume cnfcom.x: |- X = ( u e. ( F ` W ) , v e. ( _om ^o W ) |-> ( ( ( F ` W ) .o v ) +o u ) )
  assume cnfcom.y: |- Y = ( u e. ( F ` W ) , v e. ( _om ^o W ) |-> ( ( ( _om ^o W ) .o u ) +o v ) )
  assume cnfcom.n: |- N = ( ( X o. `' Y ) o. ( T ` dom G ) )

  disjoint k x
  disjoint k z
  disjoint A k
  disjoint x z
  disjoint A x
  disjoint A z
  disjoint k u
  disjoint k v
  disjoint u v
  disjoint u x
  disjoint u z
  disjoint v x
  disjoint v z
  disjoint M x
  disjoint ph u
  disjoint ph v
  disjoint f k
  disjoint f u
  disjoint f v
  disjoint f x
  disjoint f z
  disjoint F f
  disjoint F k
  disjoint F u
  disjoint F v
  disjoint F x
  disjoint F z
  disjoint K u
  disjoint K v
  disjoint T u
  disjoint T v
  disjoint T z
  disjoint W u
  disjoint W v
  disjoint W x
  disjoint G f
  disjoint G k
  disjoint G u
  disjoint G v
  disjoint G x
  disjoint G z
  disjoint H f
  disjoint H u
  disjoint H v
  disjoint H x
  disjoint S k
  disjoint S z
  disjoint k ph
  disjoint ph x
  disjoint ph z
  disjoint k w
  disjoint k y
  disjoint I k
  disjoint u w
  disjoint u y
  disjoint I u
  disjoint v w
  disjoint v y
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
  disjoint ph w
  disjoint ph y
  disjoint f w
  disjoint f y
  disjoint F w
  disjoint F y
  disjoint K w
  disjoint T w
  disjoint T y
  disjoint G w
  disjoint G y
  disjoint H w
  disjoint H y
  assert |- ( ph -> N : B -1-1-onto-> ( _om ^o W ) )

  proof
    wph
    cB
    com
    cW
    coe
    co
    #
    cX
    cY
    ccnv
    ccom
    #
    cG
    cdm
    #
    cT
    cfv
    #
    ccom
    #
    wf1o
    #
    cB
    @0
    cN
    wf1o
    #
    wph
    @0
    cW
    cF
    cfv
    #
    comu
    co
    #
    @0
    @1
    wf1o
    #
    cB
    @8
    @3
    wf1o
    @5
    wph
    @8
    @7
    @0
    comu
    co
    #
    @1
    wf1o
    #
    @9
    wph
    @0
    con0
    wcel
    #
    @7
    con0
    wcel
    #
    @11
    wph
    com
    con0
    wcel
    #
    cW
    con0
    wcel
    #
    @12
    omelon
    wph
    cA
    con0
    wcel
    #
    cW
    cA
    wcel
    #
    @15
    cnfcom.a
    wph
    cF
    c0
    csupp
    co
    #
    cA
    cW
    wph
    cF
    cdm
    #
    @18
    cA
    cF
    c0
    suppssdm
    wph
    cA
    com
    cF
    wf
    #
    @19
    cA
    wceq
    wph
    @20
    cF
    c0
    cfsupp
    wbr
    #
    wph
    cF
    cS
    wcel
    @20
    @21
    wa
    wph
    cF
    cB
    com
    cA
    ccnf
    co
    #
    ccnv
    #
    cfv
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
    @23
    wph
    cS
    @24
    @22
    wf1o
    @24
    cS
    @23
    wf1o
    @24
    cS
    @23
    wf
    wph
    com
    cA
    cS
    cnfcom.s
    @14
    wph
    omelon
    a1i
    #
    cnfcom.a
    cantnff1o
    cS
    @24
    @22
    f1ocnv
    @24
    cS
    @23
    f1of
    3syl
    cnfcom.b
    ffvelrnd
    syl5eqel
    wph
    com
    cA
    cS
    cF
    cnfcom.s
    @25
    cnfcom.a
    cantnfs
    mpbid
    simpld
    #
    cA
    com
    cF
    fdm
    syl
    syl5sseq
    wph
    cW
    @2
    cuni
    #
    cG
    cfv
    #
    @18
    cnfcom.w
    wph
    @27
    @2
    wcel
    @28
    @18
    wcel
    wph
    @27
    @27
    csuc
    @2
    @27
    @2
    @2
    con0
    @18
    cvv
    wcel
    @2
    con0
    wcel
    cF
    c0
    csupp
    ovex
    @18
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
    wph
    com
    cB
    c0
    cnfcom3.1
    c0
    com
    wcel
    wph
    peano1
    a1i
    sseldd
    #
    cnfcom2lem
    syl5eleqr
    @2
    @18
    @27
    cG
    @18
    cep
    cG
    cnfcom.g
    oif
    ffvelrni
    syl
    syl5eqel
    #
    sseldd
    #
    cA
    cW
    onelon
    syl2anc
    #
    com
    cW
    oecl
    sylancr
    wph
    @7
    com
    wcel
    #
    @13
    wph
    cA
    com
    cW
    cF
    @26
    @31
    ffvelrnd
    #
    @7
    nnon
    #
    syl
    vu
    vv
    @0
    @7
    cY
    cX
    cnfcom.y
    cnfcom.x
    omf1o
    syl2anc
    wph
    @10
    @0
    wceq
    #
    @11
    @9
    wb
    wph
    @33
    c0
    @7
    wcel
    #
    @15
    c0
    cW
    wcel
    #
    @36
    @34
    wph
    @37
    @7
    c0
    wne
    #
    wph
    cW
    @18
    wcel
    #
    @39
    @30
    wph
    @40
    @17
    @39
    wa
    #
    @39
    wph
    cF
    cA
    wfn
    #
    @16
    c0
    cvv
    wcel
    #
    @40
    @41
    wb
    wph
    @20
    @42
    @26
    cA
    com
    cF
    ffn
    syl
    cnfcom.a
    @43
    wph
    0ex
    a1i
    cW
    cF
    con0
    cvv
    cA
    c0
    elsuppfn
    syl3anc
    @17
    @39
    simpr
    syl6bi
    mpd
    wph
    @33
    @13
    @37
    @39
    wb
    @34
    @35
    @7
    on0eln0
    3syl
    mpbird
    @32
    wph
    cW
    con0
    c1o
    cdif
    wcel
    #
    @38
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
    cnfcom3.1
    cnfcom3lem
    @44
    @15
    @38
    cW
    ondif1
    simprbi
    syl
    @7
    cW
    omabs
    syl22anc
    @10
    @0
    @8
    @1
    f1oeq3
    syl
    mpbid
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
    @29
    cnfcom2
    cB
    @8
    @0
    @1
    @3
    f1oco
    syl2anc
    cN
    @4
    wceq
    @6
    @5
    wb
    cnfcom.n
    cB
    @0
    cN
    @4
    f1oeq1
    ax-mp
    sylibr
end
