include "con0.mm"
include "wcel.mm"
include "c0.mm"
include "wne.mm"
include "c1o.mm"
include "cdif.mm"
include "cdm.mm"
include "cuni.mm"
include "cfv.mm"
include "csupp.mm"
include "co.mm"
include "suppssdm.mm"
include "com.mm"
include "wf.mm"
include "wceq.mm"
include "cfsupp.mm"
include "wbr.mm"
include "wa.mm"
include "ccnf.mm"
include "ccnv.mm"
include "coe.mm"
include "wf1o.mm"
include "omelon.mm"
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
include "wn.mm"
include "wss.mm"
include "wb.mm"
include "oecl.mm"
include "sylancr.mm"
include "ontri1.mm"
include "fveq2i.mm"
include "f1ocnvfv2.mm"
include "syl5eq.mm"
include "adantr.mm"
include "1on.mm"
include "cv.mm"
include "wiso.mm"
include "wwe.mm"
include "ovexd.mm"
include "cantnfcl.mm"
include "oiiso.mm"
include "ad2antrr.mm"
include "isof1o.mm"
include "ffvelrn.mm"
include "sylancom.mm"
include "elssuni.mm"
include "onuni.mm"
include "sylancl.mm"
include "isorel.mm"
include "syl12anc.mm"
include "fvex.mm"
include "epelc.mm"
include "breq1i.mm"
include "bitr3i.mm"
include "3bitr3g.mm"
include "simplr.mm"
include "eleq12d.mm"
include "bitrd.mm"
include "mtbid.mm"
include "wo.mm"
include "onss.mm"
include "sstrd.mm"
include "sselda.mm"
include "on0eqel.mm"
include "ord.mm"
include "mt3d.mm"
include "el1o.mm"
include "sylibr.mm"
include "ex.mm"
include "ssrdv.mm"
include "cantnflt2.mm"
include "oe1.mm"
include "syl6eleq.mm"
include "eqeltrrd.mm"
include "necon3bd.mm"
include "mpd.mm"
include "dif1o.mm"
include "sylanbrc.mm"

theorem cnfcom3lem
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
  assume cnfcom3.1: |- ( ph -> _om C_ B )

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
  assert |- ( ph -> W e. ( On \ 1o ) )

  proof
    wph
    cW
    con0
    wcel
    cW
    c0
    wne
    #
    cW
    con0
    c1o
    cdif
    wcel
    wph
    cW
    cG
    cdm
    #
    cuni
    #
    cG
    cfv
    #
    con0
    cnfcom.w
    wph
    cA
    con0
    wcel
    #
    @3
    cA
    wcel
    @3
    con0
    wcel
    cnfcom.a
    wph
    cF
    c0
    csupp
    co
    #
    cA
    @3
    wph
    cF
    cdm
    #
    @5
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
    @6
    cA
    wceq
    wph
    @7
    cF
    c0
    cfsupp
    wbr
    #
    wph
    cF
    cS
    wcel
    #
    @7
    @8
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
    #
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
    @11
    wph
    cS
    @13
    @10
    wf1o
    #
    @13
    cS
    @11
    wf1o
    @13
    cS
    @11
    wf
    wph
    com
    cA
    cS
    cnfcom.s
    com
    con0
    wcel
    #
    wph
    omelon
    a1i
    #
    cnfcom.a
    cantnff1o
    #
    cS
    @13
    @10
    f1ocnv
    @13
    cS
    @11
    f1of
    3syl
    cnfcom.b
    ffvelrnd
    syl5eqel
    #
    wph
    com
    cA
    cS
    cF
    cnfcom.s
    @16
    cnfcom.a
    cantnfs
    mpbid
    simpld
    cA
    com
    cF
    fdm
    syl
    syl5sseq
    #
    wph
    @2
    @1
    wcel
    #
    @3
    @5
    wcel
    wph
    @2
    @2
    csuc
    @1
    @2
    @1
    @1
    con0
    @5
    cvv
    wcel
    #
    @1
    con0
    wcel
    #
    cF
    c0
    csupp
    ovex
    @5
    cep
    cG
    cvv
    cnfcom.g
    oion
    ax-mp
    #
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
    #
    wph
    peano1
    a1i
    sseldd
    cnfcom2lem
    syl5eleqr
    #
    @1
    @5
    @2
    cG
    @5
    cep
    cG
    cnfcom.g
    oif
    ffvelrni
    syl
    sseldd
    cA
    @3
    onelon
    syl2anc
    syl5eqel
    wph
    cB
    com
    wcel
    #
    wn
    #
    @0
    wph
    com
    cB
    wss
    #
    @27
    cnfcom3.1
    wph
    @15
    cB
    con0
    wcel
    #
    @28
    @27
    wb
    omelon
    wph
    @13
    con0
    wcel
    #
    cB
    @13
    wcel
    #
    @29
    wph
    @15
    @4
    @30
    omelon
    cnfcom.a
    com
    cA
    oecl
    sylancr
    cnfcom.b
    @13
    cB
    onelon
    syl2anc
    com
    cB
    ontri1
    sylancr
    mpbid
    wph
    @26
    cW
    c0
    wph
    cW
    c0
    wceq
    #
    @26
    wph
    @32
    wa
    #
    cF
    @10
    cfv
    #
    cB
    com
    wph
    @34
    cB
    wceq
    @32
    wph
    @34
    @12
    @10
    cfv
    #
    cB
    cF
    @12
    @10
    cnfcom.f
    fveq2i
    wph
    @14
    @31
    @35
    cB
    wceq
    @17
    cnfcom.b
    cS
    @13
    cB
    @10
    f1ocnvfv2
    syl2anc
    syl5eq
    adantr
    @33
    @34
    com
    c1o
    coe
    co
    #
    com
    @33
    com
    cA
    c1o
    cS
    cF
    cnfcom.s
    @15
    @33
    omelon
    a1i
    wph
    @4
    @32
    cnfcom.a
    adantr
    wph
    @9
    @32
    @18
    adantr
    @24
    @33
    peano1
    a1i
    c1o
    con0
    wcel
    @33
    1on
    a1i
    @33
    vx
    @5
    c1o
    @33
    vx
    cv
    #
    @5
    wcel
    #
    @37
    c1o
    wcel
    #
    @33
    @38
    wa
    #
    @37
    c0
    wceq
    #
    @39
    @40
    @41
    c0
    @37
    wcel
    #
    @40
    @2
    @37
    cG
    ccnv
    #
    cfv
    #
    wcel
    #
    @42
    @40
    @44
    @2
    wss
    #
    @45
    wn
    #
    @40
    @44
    @1
    wcel
    #
    @46
    @33
    @38
    @5
    @1
    @43
    wf
    #
    @48
    @40
    @1
    @5
    cG
    wf1o
    #
    @5
    @1
    @43
    wf1o
    @49
    @40
    @1
    @5
    cep
    cep
    cG
    wiso
    #
    @50
    wph
    @51
    @32
    @38
    wph
    @21
    @5
    cep
    wwe
    #
    @51
    wph
    cF
    c0
    csupp
    ovexd
    wph
    @52
    @1
    com
    wcel
    wph
    com
    cA
    cS
    cF
    cG
    cnfcom.s
    @16
    cnfcom.a
    cnfcom.g
    @18
    cantnfcl
    simpld
    @5
    cep
    cG
    cvv
    cnfcom.g
    oiiso
    syl2anc
    ad2antrr
    #
    @1
    @5
    cep
    cep
    cG
    isof1o
    syl
    #
    @1
    @5
    cG
    f1ocnv
    @5
    @1
    @43
    f1of
    3syl
    @5
    @1
    @37
    @43
    ffvelrn
    sylancom
    #
    @44
    @1
    elssuni
    syl
    @40
    @44
    con0
    wcel
    #
    @2
    con0
    wcel
    #
    @46
    @47
    wb
    @40
    @22
    @48
    @56
    @23
    @55
    @1
    @44
    onelon
    sylancr
    @22
    @57
    @23
    @1
    onuni
    ax-mp
    @44
    @2
    ontri1
    sylancl
    mpbid
    @40
    @45
    cW
    @44
    cG
    cfv
    #
    wcel
    #
    @42
    @40
    @2
    @44
    cep
    wbr
    #
    @3
    @58
    cep
    wbr
    #
    @45
    @59
    @40
    @51
    @20
    @48
    @60
    @61
    wb
    @53
    wph
    @20
    @32
    @38
    @25
    ad2antrr
    @55
    @1
    @5
    @2
    @44
    cep
    cep
    cG
    isorel
    syl12anc
    @2
    @44
    @37
    @43
    fvex
    epelc
    @61
    cW
    @58
    cep
    wbr
    @59
    cW
    @3
    @58
    cep
    cnfcom.w
    breq1i
    cW
    @58
    @44
    cG
    fvex
    epelc
    bitr3i
    3bitr3g
    @40
    cW
    c0
    @58
    @37
    wph
    @32
    @38
    simplr
    @33
    @38
    @50
    @58
    @37
    wceq
    @54
    @1
    @5
    @37
    cG
    f1ocnvfv2
    sylancom
    eleq12d
    bitrd
    mtbid
    @40
    @41
    @42
    @40
    @37
    con0
    wcel
    @41
    @42
    wo
    @33
    @5
    con0
    @37
    wph
    @5
    con0
    wss
    @32
    wph
    @5
    cA
    con0
    @19
    wph
    @4
    cA
    con0
    wss
    cnfcom.a
    cA
    onss
    syl
    sstrd
    adantr
    sselda
    @37
    on0eqel
    syl
    ord
    mt3d
    @37
    el1o
    sylibr
    ex
    ssrdv
    cantnflt2
    @15
    @36
    com
    wceq
    omelon
    com
    oe1
    ax-mp
    syl6eleq
    eqeltrrd
    ex
    necon3bd
    mpd
    cW
    con0
    dif1o
    sylanbrc
end
