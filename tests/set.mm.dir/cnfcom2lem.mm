include "cdm.mm"
include "cuni.mm"
include "wceq.mm"
include "wn.mm"
include "csuc.mm"
include "c0.mm"
include "wlim.mm"
include "wo.mm"
include "wcel.mm"
include "n0i.mm"
include "syl.mm"
include "wa.mm"
include "com.mm"
include "ccnf.mm"
include "co.mm"
include "cfv.mm"
include "csn.mm"
include "cxp.mm"
include "cmpt.mm"
include "cv.mm"
include "wf.mm"
include "cfsupp.mm"
include "wbr.mm"
include "ccnv.mm"
include "coe.mm"
include "wf1o.mm"
include "con0.mm"
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
include "adantr.mm"
include "feqmptd.mm"
include "cdif.mm"
include "dif0.mm"
include "eleq2i.mm"
include "cvv.mm"
include "csupp.mm"
include "wss.mm"
include "cen.mm"
include "simpr.mm"
include "cep.mm"
include "wwe.mm"
include "suppssdm.mm"
include "fdm.mm"
include "syl5sseq.mm"
include "ssexd.mm"
include "cantnfcl.mm"
include "oien.mm"
include "syl2anc.mm"
include "eqbrtrrd.mm"
include "ensymd.mm"
include "en0.mm"
include "sylib.mm"
include "ss0b.mm"
include "sylibr.mm"
include "0ex.mm"
include "suppssr.mm"
include "sylan2br.mm"
include "mpteq2dva.mm"
include "eqtrd.mm"
include "fconstmpt.mm"
include "syl6eqr.mm"
include "fveq2d.mm"
include "fveq2i.mm"
include "f1ocnvfv2.mm"
include "syl5eq.mm"
include "peano1.mm"
include "cantnf0.mm"
include "3eqtr3d.mm"
include "mtand.mm"
include "simprd.mm"
include "nnlim.mm"
include "ioran.mm"
include "sylanbrc.mm"
include "word.mm"
include "wb.mm"
include "oicl.mm"
include "unizlim.mm"
include "ax-mp.mm"
include "sylnibr.mm"
include "orduniorsuc.mm"
include "mp1i.mm"
include "ord.mm"
include "mpd.mm"

theorem cnfcom2lem
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
  assert |- ( ph -> dom G = suc U. dom G )

  proof
    wph
    cG
    cdm
    #
    @0
    cuni
    #
    wceq
    #
    wn
    @0
    @1
    csuc
    wceq
    #
    wph
    @0
    c0
    wceq
    #
    @0
    wlim
    #
    wo
    #
    @2
    wph
    @4
    wn
    @5
    wn
    #
    @6
    wn
    wph
    @4
    cB
    c0
    wceq
    #
    wph
    c0
    cB
    wcel
    @8
    wn
    cnfcom2.1
    cB
    c0
    n0i
    syl
    wph
    @4
    wa
    #
    cF
    com
    cA
    ccnf
    co
    #
    cfv
    #
    cA
    c0
    csn
    cxp
    #
    @10
    cfv
    #
    cB
    c0
    @9
    cF
    @12
    @10
    @9
    cF
    vx
    cA
    c0
    cmpt
    #
    @12
    @9
    cF
    vx
    cA
    vx
    cv
    #
    cF
    cfv
    #
    cmpt
    @14
    @9
    vx
    cA
    com
    cF
    wph
    cA
    com
    cF
    wf
    #
    @4
    wph
    @17
    cF
    c0
    cfsupp
    wbr
    #
    wph
    cF
    cS
    wcel
    @17
    @18
    wa
    wph
    cF
    cB
    @10
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
    @19
    wph
    cS
    @21
    @10
    wf1o
    #
    @21
    cS
    @19
    wf1o
    @21
    cS
    @19
    wf
    wph
    com
    cA
    cS
    cnfcom.s
    com
    con0
    wcel
    wph
    omelon
    a1i
    #
    cnfcom.a
    cantnff1o
    #
    cS
    @21
    @10
    f1ocnv
    @21
    cS
    @19
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
    @23
    cnfcom.a
    cantnfs
    mpbid
    simpld
    #
    adantr
    #
    feqmptd
    @9
    vx
    cA
    @16
    c0
    @15
    cA
    wcel
    @9
    @15
    cA
    c0
    cdif
    #
    wcel
    @16
    c0
    wceq
    @28
    cA
    @15
    cA
    dif0
    eleq2i
    @9
    cA
    com
    cvv
    cF
    con0
    c0
    @15
    c0
    @27
    @9
    cF
    c0
    csupp
    co
    #
    c0
    wceq
    #
    @29
    c0
    wss
    @9
    @29
    c0
    cen
    wbr
    @30
    @9
    c0
    @29
    @9
    @0
    c0
    @29
    cen
    wph
    @4
    simpr
    wph
    @0
    @29
    cen
    wbr
    #
    @4
    wph
    @29
    cvv
    wcel
    @29
    cep
    wwe
    #
    @31
    wph
    @29
    cA
    con0
    cnfcom.a
    wph
    cF
    cdm
    #
    @29
    cA
    cF
    c0
    suppssdm
    wph
    @17
    @33
    cA
    wceq
    @26
    cA
    com
    cF
    fdm
    syl
    syl5sseq
    ssexd
    wph
    @32
    @0
    com
    wcel
    #
    wph
    com
    cA
    cS
    cF
    cG
    cnfcom.s
    @23
    cnfcom.a
    cnfcom.g
    @25
    cantnfcl
    #
    simpld
    @29
    cep
    cG
    cvv
    cnfcom.g
    oien
    syl2anc
    adantr
    eqbrtrrd
    ensymd
    @29
    en0
    sylib
    @29
    ss0b
    sylibr
    wph
    cA
    con0
    wcel
    @4
    cnfcom.a
    adantr
    c0
    cvv
    wcel
    @9
    0ex
    a1i
    suppssr
    sylan2br
    mpteq2dva
    eqtrd
    vx
    cA
    c0
    fconstmpt
    syl6eqr
    fveq2d
    wph
    @11
    cB
    wceq
    @4
    wph
    @11
    @20
    @10
    cfv
    #
    cB
    cF
    @20
    @10
    cnfcom.f
    fveq2i
    wph
    @22
    cB
    @21
    wcel
    @36
    cB
    wceq
    @24
    cnfcom.b
    cS
    @21
    cB
    @10
    f1ocnvfv2
    syl2anc
    syl5eq
    adantr
    wph
    @13
    c0
    wceq
    @4
    wph
    com
    cA
    cS
    cnfcom.s
    @23
    cnfcom.a
    c0
    com
    wcel
    wph
    peano1
    a1i
    cantnf0
    adantr
    3eqtr3d
    mtand
    wph
    @34
    @7
    wph
    @32
    @34
    @35
    simprd
    @0
    nnlim
    syl
    @4
    @5
    ioran
    sylanbrc
    @0
    word
    #
    @2
    @6
    wb
    @29
    cep
    cG
    cnfcom.g
    oicl
    #
    @0
    unizlim
    ax-mp
    sylnibr
    wph
    @2
    @3
    @37
    @2
    @3
    wo
    wph
    @38
    @0
    orduniorsuc
    mp1i
    ord
    mpd
end
