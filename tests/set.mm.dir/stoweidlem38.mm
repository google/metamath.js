include "wcel.mm"
include "wa.mm"
include "cc0.mm"
include "cfv.mm"
include "cle.mm"
include "wbr.mm"
include "c1.mm"
include "cdiv.mm"
include "co.mm"
include "cfz.mm"
include "cv.mm"
include "csu.mm"
include "cmul.mm"
include "cr.mm"
include "nnrecred.mm"
include "adantr.mm"
include "fzfid.mm"
include "stoweidlem15.mm"
include "simp1d.mm"
include "an32s.mm"
include "fsumrecl.mm"
include "clt.mm"
include "1red.mm"
include "0le1.mm"
include "a1i.mm"
include "nnred.mm"
include "nngt0d.mm"
include "divge0.mm"
include "syl22anc.mm"
include "simp2d.mm"
include "fsumge0.mm"
include "mulge0d.mm"
include "stoweidlem30.mm"
include "breqtrrd.mm"
include "simp3d.mm"
include "fsumle.mm"
include "wceq.mm"
include "chash.mm"
include "cfn.mm"
include "cc.mm"
include "ax-1cn.mm"
include "fsumconst.mm"
include "sylancl.mm"
include "cn0.mm"
include "nnnn0d.mm"
include "hashfz1.mm"
include "syl.mm"
include "oveq1d.mm"
include "nncnd.mm"
include "mulid1d.mm"
include "3eqtrd.mm"
include "breqtrd.mm"
include "wb.mm"
include "0lt1.mm"
include "jca.mm"
include "divgt0.mm"
include "syl21anc.mm"
include "lemul2.mm"
include "syl112anc.mm"
include "mpbid.mm"
include "eqbrtrd.mm"
include "wne.mm"
include "w3a.mm"
include "nnne0d.mm"
include "3jca.mm"
include "divcan1.mm"

theorem stoweidlem38
  let wph: wff ph
  let vt: setvar t
  let cA: class A
  let cP: class P
  let cQ: class Q
  let cS: class S
  let cT: class T
  let vf: setvar f
  let vh: setvar h
  let vi: setvar i
  let cG: class G
  let cM: class M
  let cZ: class Z
  let vk: setvar k
  let vx: setvar x
  assume stoweidlem38.1: |- Q = { h e. A | ( ( h ` Z ) = 0 /\ A. t e. T ( 0 <_ ( h ` t ) /\ ( h ` t ) <_ 1 ) ) }
  assume stoweidlem38.2: |- P = ( t e. T |-> ( ( 1 / M ) x. sum_ i e. ( 1 ... M ) ( ( G ` i ) ` t ) ) )
  assume stoweidlem38.3: |- ( ph -> M e. NN )
  assume stoweidlem38.4: |- ( ph -> G : ( 1 ... M ) --> Q )
  assume stoweidlem38.5: |- ( ( ph /\ f e. A ) -> f : T --> RR )

  disjoint f i
  disjoint T f
  disjoint T i
  disjoint A f
  disjoint G f
  disjoint f ph
  disjoint i ph
  disjoint h i
  disjoint h t
  disjoint T h
  disjoint i t
  disjoint T t
  disjoint A h
  disjoint G h
  disjoint G t
  disjoint Z h
  disjoint M i
  disjoint M t
  disjoint S i
  disjoint k x
  assert |- ( ( ph /\ S e. T ) -> ( 0 <_ ( P ` S ) /\ ( P ` S ) <_ 1 ) )

  proof
    wph
    cS
    cT
    wcel
    #
    wa
    #
    cc0
    cS
    cP
    cfv
    #
    cle
    wbr
    @2
    c1
    cle
    wbr
    @1
    cc0
    c1
    cM
    cdiv
    co
    #
    c1
    cM
    cfz
    co
    #
    cS
    vi
    cv
    #
    cG
    cfv
    cfv
    #
    vi
    csu
    #
    cmul
    co
    #
    @2
    cle
    @1
    @3
    @7
    wph
    @3
    cr
    wcel
    #
    @0
    wph
    cM
    stoweidlem38.3
    nnrecred
    adantr
    #
    @1
    @4
    @6
    vi
    @1
    c1
    cM
    fzfid
    #
    wph
    @5
    @4
    wcel
    #
    @0
    @6
    cr
    wcel
    #
    wph
    @12
    wa
    @0
    wa
    #
    @13
    cc0
    @6
    cle
    wbr
    #
    @6
    c1
    cle
    wbr
    #
    wph
    vt
    cA
    cQ
    cS
    cT
    vf
    vh
    cG
    @5
    cM
    cZ
    stoweidlem38.1
    stoweidlem38.4
    stoweidlem38.5
    stoweidlem15
    #
    simp1d
    an32s
    #
    fsumrecl
    #
    wph
    cc0
    @3
    cle
    wbr
    #
    @0
    wph
    c1
    cr
    wcel
    #
    cc0
    c1
    cle
    wbr
    #
    cM
    cr
    wcel
    #
    cc0
    cM
    clt
    wbr
    #
    @20
    wph
    1red
    @22
    wph
    0le1
    a1i
    wph
    cM
    stoweidlem38.3
    nnred
    #
    wph
    cM
    stoweidlem38.3
    nngt0d
    #
    c1
    cM
    divge0
    syl22anc
    adantr
    @1
    @4
    @6
    vi
    @11
    @18
    wph
    @12
    @0
    @15
    @14
    @13
    @15
    @16
    @17
    simp2d
    an32s
    fsumge0
    mulge0d
    wph
    vt
    cA
    cP
    cQ
    cS
    cT
    vf
    vh
    vi
    cG
    cM
    cZ
    stoweidlem38.1
    stoweidlem38.2
    stoweidlem38.3
    stoweidlem38.4
    stoweidlem38.5
    stoweidlem30
    #
    breqtrrd
    @1
    @2
    @3
    cM
    cmul
    co
    #
    c1
    cle
    @1
    @2
    @8
    @28
    cle
    @27
    @1
    @7
    cM
    cle
    wbr
    #
    @8
    @28
    cle
    wbr
    #
    @1
    @7
    @4
    c1
    vi
    csu
    #
    cM
    cle
    @1
    @4
    @6
    c1
    vi
    @11
    @18
    @1
    @12
    wa
    1red
    wph
    @12
    @0
    @16
    @14
    @13
    @15
    @16
    @17
    simp3d
    an32s
    fsumle
    wph
    @31
    cM
    wceq
    @0
    wph
    @31
    @4
    chash
    cfv
    #
    c1
    cmul
    co
    #
    cM
    c1
    cmul
    co
    cM
    wph
    @4
    cfn
    wcel
    c1
    cc
    wcel
    #
    @31
    @33
    wceq
    wph
    c1
    cM
    fzfid
    ax-1cn
    @4
    c1
    vi
    fsumconst
    sylancl
    wph
    @32
    cM
    c1
    cmul
    wph
    cM
    cn0
    wcel
    @32
    cM
    wceq
    wph
    cM
    stoweidlem38.3
    nnnn0d
    cM
    hashfz1
    syl
    oveq1d
    wph
    cM
    wph
    cM
    stoweidlem38.3
    nncnd
    #
    mulid1d
    3eqtrd
    adantr
    breqtrd
    @1
    @7
    cr
    wcel
    @23
    @9
    cc0
    @3
    clt
    wbr
    #
    @29
    @30
    wb
    @19
    wph
    @23
    @0
    @25
    adantr
    @10
    @1
    @21
    cc0
    c1
    clt
    wbr
    #
    @23
    @24
    wa
    #
    @36
    @1
    1red
    @37
    @1
    0lt1
    a1i
    wph
    @38
    @0
    wph
    @23
    @24
    @25
    @26
    jca
    adantr
    c1
    cM
    divgt0
    syl21anc
    @7
    cM
    @3
    lemul2
    syl112anc
    mpbid
    eqbrtrd
    @1
    @34
    cM
    cc
    wcel
    #
    cM
    cc0
    wne
    #
    w3a
    #
    @28
    c1
    wceq
    wph
    @41
    @0
    wph
    @34
    @39
    @40
    @34
    wph
    ax-1cn
    a1i
    @35
    wph
    cM
    stoweidlem38.3
    nnne0d
    3jca
    adantr
    c1
    cM
    divcan1
    syl
    breqtrd
    jca
end
