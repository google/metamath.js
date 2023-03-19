include "cv.mm"
include "cfv.mm"
include "c1.mm"
include "caddc.mm"
include "co.mm"
include "wceq.mm"
include "ciedg.mm"
include "csn.mm"
include "cpr.mm"
include "wss.mm"
include "wif.mm"
include "cc0.mm"
include "chash.mm"
include "cfzo.mm"
include "wral.mm"
include "w3a.mm"
include "wlkp1lem6.mm"
include "cwlks.mm"
include "wbr.mm"
include "cdm.mm"
include "cword.mm"
include "wcel.mm"
include "cfz.mm"
include "wf.mm"
include "cvv.mm"
include "wb.mm"
include "cedg.mm"
include "elfvexd.mm"
include "iswlkg.mm"
include "syl.mm"
include "eqcomi.mm"
include "oveq2i.mm"
include "raleqi.mm"
include "biimpi.mm"
include "3ad2ant3.mm"
include "syl6bi.mm"
include "mpd.mm"
include "eqeq12.mm"
include "3adant3.mm"
include "simp3.mm"
include "simp1.mm"
include "sneqd.mm"
include "eqeq12d.mm"
include "preq12.mm"
include "sseq12d.mm"
include "ifpbi123d.mm"
include "biimprd.mm"
include "ral2imi.mm"
include "sylc.mm"
include "wa.mm"
include "cop.mm"
include "cun.mm"
include "wlkp1lem3.mm"
include "adantr.mm"
include "wn.mm"
include "3jca.mm"
include "fsnunfv.mm"
include "wi.mm"
include "fveq2.mm"
include "wlkp1lem5.mm"
include "cn0.mm"
include "cuz.mm"
include "wlkf.mm"
include "lencl.mm"
include "eleq1i.mm"
include "elnn0uz.mm"
include "sylbb1.mm"
include "3syl.mm"
include "sylibr.mm"
include "nn0fz0.mm"
include "sylib.mm"
include "rspcdva.mm"
include "fveq1i.mm"
include "ovex.mm"
include "wlkp1lem1.mm"
include "mp3an2i.mm"
include "syl5eq.mm"
include "eqeq2d.mm"
include "eqcom.mm"
include "syl6bb.mm"
include "sneq.mm"
include "adantl.mm"
include "eqtrd.mm"
include "ex.mm"
include "sylbid.mm"
include "eqeq1.mm"
include "imbi12d.mm"
include "syl5ibrcom.mm"
include "imp.mm"
include "3eqtrd.mm"
include "wlkp1lem7.mm"
include "ifpimpda.mm"
include "wlkp1lem2.mm"
include "oveq2d.mm"
include "fzosplitsn.mm"
include "raleqdv.mm"
include "ralunb.mm"
include "a1i.mm"
include "fvex.mm"
include "eqeltri.mm"
include "oveq1.mm"
include "fveq2d.mm"
include "preq12d.mm"
include "ralsng.mm"
include "mp1i.mm"
include "anbi2d.mm"
include "3bitrd.mm"
include "mpbir2and.mm"

theorem wlkp1lem8
  let wph: wff ph
  let cB: class B
  let cC: class C
  let cP: class P
  let cQ: class Q
  let cS: class S
  let vk: setvar k
  let cE: class E
  let cF: class F
  let cG: class G
  let cH: class H
  let cI: class I
  let cN: class N
  let cV: class V
  let vx: setvar x
  assume wlkp1.v: |- V = ( Vtx ` G )
  assume wlkp1.i: |- I = ( iEdg ` G )
  assume wlkp1.f: |- ( ph -> Fun I )
  assume wlkp1.a: |- ( ph -> I e. Fin )
  assume wlkp1.b: |- ( ph -> B e. _V )
  assume wlkp1.c: |- ( ph -> C e. V )
  assume wlkp1.d: |- ( ph -> -. B e. dom I )
  assume wlkp1.w: |- ( ph -> F ( Walks ` G ) P )
  assume wlkp1.n: |- N = ( # ` F )
  assume wlkp1.e: |- ( ph -> E e. ( Edg ` G ) )
  assume wlkp1.x: |- ( ph -> { ( P ` N ) , C } C_ E )
  assume wlkp1.u: |- ( ph -> ( iEdg ` S ) = ( I u. { <. B , E >. } ) )
  assume wlkp1.h: |- H = ( F u. { <. N , B >. } )
  assume wlkp1.q: |- Q = ( P u. { <. ( N + 1 ) , C >. } )
  assume wlkp1.s: |- ( ph -> ( Vtx ` S ) = V )
  assume wlkp1.l: |- ( ( ph /\ C = ( P ` N ) ) -> E = { C } )

  disjoint k ph
  disjoint N k
  disjoint P k
  disjoint Q k
  disjoint F k
  disjoint G k
  disjoint H k
  disjoint S k
  disjoint ph x
  disjoint k x
  disjoint N x
  disjoint P x
  disjoint Q x
  assert |- ( ph -> A. k e. ( 0 ..^ ( # ` H ) ) if- ( ( Q ` k ) = ( Q ` ( k + 1 ) ) , ( ( iEdg ` S ) ` ( H ` k ) ) = { ( Q ` k ) } , { ( Q ` k ) , ( Q ` ( k + 1 ) ) } C_ ( ( iEdg ` S ) ` ( H ` k ) ) ) )

  proof
    wph
    vk
    cv
    #
    cQ
    cfv
    #
    @0
    c1
    caddc
    co
    #
    cQ
    cfv
    #
    wceq
    #
    @0
    cH
    cfv
    #
    cS
    ciedg
    cfv
    #
    cfv
    #
    @1
    csn
    #
    wceq
    #
    @1
    @3
    cpr
    #
    @7
    wss
    #
    wif
    #
    vk
    cc0
    cH
    chash
    cfv
    #
    cfzo
    co
    #
    wral
    #
    @12
    vk
    cc0
    cN
    cfzo
    co
    #
    wral
    #
    cN
    cQ
    cfv
    #
    cN
    c1
    caddc
    co
    #
    cQ
    cfv
    #
    wceq
    #
    cN
    cH
    cfv
    #
    @6
    cfv
    #
    @18
    csn
    #
    wceq
    #
    @18
    @20
    cpr
    #
    @23
    wss
    #
    wif
    #
    wph
    @1
    @0
    cP
    cfv
    #
    wceq
    #
    @3
    @2
    cP
    cfv
    #
    wceq
    #
    @7
    @0
    cF
    cfv
    cI
    cfv
    #
    wceq
    #
    w3a
    #
    vk
    @16
    wral
    @29
    @31
    wceq
    #
    @33
    @29
    csn
    #
    wceq
    #
    @29
    @31
    cpr
    #
    @33
    wss
    #
    wif
    #
    vk
    @16
    wral
    #
    @17
    wph
    cB
    cC
    cP
    cQ
    cS
    vk
    cE
    cF
    cG
    cH
    cI
    cN
    cV
    wlkp1.v
    wlkp1.i
    wlkp1.f
    wlkp1.a
    wlkp1.b
    wlkp1.c
    wlkp1.d
    wlkp1.w
    wlkp1.n
    wlkp1.e
    wlkp1.x
    wlkp1.u
    wlkp1.h
    wlkp1.q
    wlkp1.s
    wlkp1lem6
    wph
    cF
    cP
    cG
    cwlks
    cfv
    wbr
    #
    @42
    wlkp1.w
    wph
    @43
    cF
    cI
    cdm
    #
    cword
    wcel
    #
    cc0
    cF
    chash
    cfv
    #
    cfz
    co
    cV
    cP
    wf
    #
    @41
    vk
    cc0
    @46
    cfzo
    co
    #
    wral
    #
    w3a
    #
    @42
    wph
    cG
    cvv
    wcel
    @43
    @50
    wb
    wph
    cE
    cedg
    cG
    wlkp1.e
    elfvexd
    cP
    vk
    cF
    cG
    cI
    cV
    cvv
    wlkp1.v
    wlkp1.i
    iswlkg
    syl
    @49
    @45
    @42
    @47
    @49
    @42
    @41
    vk
    @48
    @16
    @46
    cN
    cc0
    cfzo
    cN
    @46
    wlkp1.n
    eqcomi
    oveq2i
    raleqi
    biimpi
    3ad2ant3
    syl6bi
    mpd
    @35
    @41
    @12
    vk
    @16
    @35
    @12
    @41
    @35
    @4
    @9
    @11
    @36
    @38
    @40
    @30
    @32
    @4
    @36
    wb
    @34
    @1
    @29
    @3
    @31
    eqeq12
    3adant3
    @35
    @7
    @33
    @8
    @37
    @30
    @32
    @34
    simp3
    #
    @35
    @1
    @29
    @30
    @32
    @34
    simp1
    sneqd
    eqeq12d
    @35
    @10
    @39
    @7
    @33
    @30
    @32
    @10
    @39
    wceq
    @34
    @1
    @3
    @29
    @31
    preq12
    3adant3
    @51
    sseq12d
    ifpbi123d
    biimprd
    ral2imi
    sylc
    wph
    @21
    @25
    @27
    wph
    @21
    wa
    #
    @23
    cB
    cI
    cB
    cE
    cop
    csn
    cun
    cfv
    #
    cE
    @24
    wph
    @23
    @53
    wceq
    @21
    wph
    cB
    cC
    cP
    cS
    cE
    cF
    cG
    cH
    cI
    cN
    cV
    wlkp1.v
    wlkp1.i
    wlkp1.f
    wlkp1.a
    wlkp1.b
    wlkp1.c
    wlkp1.d
    wlkp1.w
    wlkp1.n
    wlkp1.e
    wlkp1.x
    wlkp1.u
    wlkp1.h
    wlkp1lem3
    adantr
    @52
    cB
    cvv
    wcel
    #
    cE
    cG
    cedg
    cfv
    #
    wcel
    #
    cB
    @44
    wcel
    wn
    #
    w3a
    #
    @53
    cE
    wceq
    wph
    @58
    @21
    wph
    @54
    @56
    @57
    wlkp1.b
    wlkp1.e
    wlkp1.d
    3jca
    adantr
    cI
    cvv
    @55
    cB
    cE
    fsnunfv
    syl
    wph
    @21
    cE
    @24
    wceq
    #
    wph
    @18
    cN
    cP
    cfv
    #
    wceq
    #
    @21
    @59
    wi
    #
    wph
    vx
    cv
    #
    cQ
    cfv
    #
    @63
    cP
    cfv
    #
    wceq
    @61
    vx
    cc0
    cN
    cfz
    co
    #
    cN
    @63
    cN
    wceq
    @64
    @18
    @65
    @60
    @63
    cN
    cQ
    fveq2
    @63
    cN
    cP
    fveq2
    eqeq12d
    wph
    cB
    cC
    cP
    cQ
    cS
    vx
    cE
    cF
    cG
    cH
    cI
    cN
    cV
    wlkp1.v
    wlkp1.i
    wlkp1.f
    wlkp1.a
    wlkp1.b
    wlkp1.c
    wlkp1.d
    wlkp1.w
    wlkp1.n
    wlkp1.e
    wlkp1.x
    wlkp1.u
    wlkp1.h
    wlkp1.q
    wlkp1.s
    wlkp1lem5
    wph
    cN
    cn0
    wcel
    #
    cN
    @66
    wcel
    wph
    cN
    cc0
    cuz
    cfv
    wcel
    #
    @67
    wph
    @43
    @45
    @68
    wlkp1.w
    cP
    cF
    cG
    cI
    wlkp1.i
    wlkf
    @45
    @46
    cn0
    wcel
    #
    @68
    @44
    cF
    lencl
    @67
    @69
    @68
    cN
    @46
    cn0
    wlkp1.n
    eleq1i
    cN
    elnn0uz
    #
    sylbb1
    syl
    3syl
    #
    @70
    sylibr
    cN
    nn0fz0
    sylib
    rspcdva
    wph
    @62
    @61
    @60
    @20
    wceq
    #
    cE
    @60
    csn
    #
    wceq
    #
    wi
    wph
    @72
    cC
    @60
    wceq
    #
    @74
    wph
    @72
    @60
    cC
    wceq
    @75
    wph
    @20
    cC
    @60
    wph
    @20
    @19
    cP
    @19
    cC
    cop
    csn
    cun
    #
    cfv
    #
    cC
    @19
    cQ
    @76
    wlkp1.q
    fveq1i
    @19
    cvv
    wcel
    wph
    cC
    cV
    wcel
    @19
    cP
    cdm
    wcel
    wn
    @77
    cC
    wceq
    cN
    c1
    caddc
    ovex
    wlkp1.c
    wph
    cB
    cC
    cP
    cF
    cG
    cI
    cN
    cV
    wlkp1.v
    wlkp1.i
    wlkp1.f
    wlkp1.a
    wlkp1.b
    wlkp1.c
    wlkp1.d
    wlkp1.w
    wlkp1.n
    wlkp1lem1
    cP
    cvv
    cV
    @19
    cC
    fsnunfv
    mp3an2i
    syl5eq
    eqeq2d
    @60
    cC
    eqcom
    syl6bb
    wph
    @75
    @74
    wph
    @75
    wa
    cE
    cC
    csn
    #
    @73
    wlkp1.l
    @75
    @78
    @73
    wceq
    wph
    cC
    @60
    sneq
    adantl
    eqtrd
    ex
    sylbid
    @61
    @21
    @72
    @59
    @74
    @18
    @60
    @20
    eqeq1
    @61
    @24
    @73
    cE
    @18
    @60
    sneq
    eqeq2d
    imbi12d
    syl5ibrcom
    mpd
    imp
    3eqtrd
    wph
    @27
    @21
    wn
    wph
    cB
    cC
    cP
    cQ
    cS
    cE
    cF
    cG
    cH
    cI
    cN
    cV
    wlkp1.v
    wlkp1.i
    wlkp1.f
    wlkp1.a
    wlkp1.b
    wlkp1.c
    wlkp1.d
    wlkp1.w
    wlkp1.n
    wlkp1.e
    wlkp1.x
    wlkp1.u
    wlkp1.h
    wlkp1.q
    wlkp1.s
    wlkp1lem7
    adantr
    ifpimpda
    wph
    @15
    @12
    vk
    @16
    cN
    csn
    #
    cun
    #
    wral
    #
    @17
    @12
    vk
    @79
    wral
    #
    wa
    #
    @17
    @28
    wa
    wph
    @12
    vk
    @14
    @80
    wph
    @14
    cc0
    @19
    cfzo
    co
    #
    @80
    wph
    @13
    @19
    cc0
    cfzo
    wph
    cB
    cC
    cP
    cS
    cE
    cF
    cG
    cH
    cI
    cN
    cV
    wlkp1.v
    wlkp1.i
    wlkp1.f
    wlkp1.a
    wlkp1.b
    wlkp1.c
    wlkp1.d
    wlkp1.w
    wlkp1.n
    wlkp1.e
    wlkp1.x
    wlkp1.u
    wlkp1.h
    wlkp1lem2
    oveq2d
    wph
    @68
    @84
    @80
    wceq
    @71
    cc0
    cN
    fzosplitsn
    syl
    eqtrd
    raleqdv
    @81
    @83
    wb
    wph
    @12
    vk
    @16
    @79
    ralunb
    a1i
    wph
    @82
    @28
    @17
    cN
    cvv
    wcel
    @82
    @28
    wb
    wph
    cN
    @46
    cvv
    wlkp1.n
    cF
    chash
    fvex
    eqeltri
    @12
    @28
    vk
    cN
    cvv
    @0
    cN
    wceq
    #
    @4
    @9
    @11
    @21
    @25
    @27
    @85
    @1
    @18
    @3
    @20
    @0
    cN
    cQ
    fveq2
    #
    @85
    @2
    @19
    cQ
    @0
    cN
    c1
    caddc
    oveq1
    fveq2d
    #
    eqeq12d
    @85
    @7
    @23
    @8
    @24
    @85
    @5
    @22
    @6
    @0
    cN
    cH
    fveq2
    fveq2d
    #
    @85
    @1
    @18
    @86
    sneqd
    eqeq12d
    @85
    @10
    @26
    @7
    @23
    @85
    @1
    @18
    @3
    @20
    @86
    @87
    preq12d
    @88
    sseq12d
    ifpbi123d
    ralsng
    mp1i
    anbi2d
    3bitrd
    mpbir2and
end
