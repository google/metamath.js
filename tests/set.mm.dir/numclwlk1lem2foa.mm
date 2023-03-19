include "cusgr.mm"
include "wcel.mm"
include "c3.mm"
include "cuz.mm"
include "cfv.mm"
include "w3a.mm"
include "cnbgr.mm"
include "co.mm"
include "wa.mm"
include "cs1.mm"
include "cconcat.mm"
include "cclwwlkn.mm"
include "cc0.mm"
include "c2.mm"
include "cmin.mm"
include "cop.mm"
include "csubstr.mm"
include "c1.mm"
include "wceq.mm"
include "cpr.mm"
include "cedg.mm"
include "cclwwlknon.mm"
include "simpl2.mm"
include "nbgrisvtx.mm"
include "ad2antll.mm"
include "simpl3.mm"
include "wi.mm"
include "nbgrsym.mm"
include "eqid.mm"
include "nbusgreledg.mm"
include "biimpd.mm"
include "syl5bi.mm"
include "adantld.mm"
include "3ad2ant1.mm"
include "imp.mm"
include "simprl.mm"
include "syl6eleq.mm"
include "clwwlknonex2.mm"
include "syl311anc.mm"
include "cword.mm"
include "chash.mm"
include "cv.mm"
include "caddc.mm"
include "cfzo.mm"
include "wral.mm"
include "clsw.mm"
include "eleq2i.mm"
include "wb.mm"
include "wne.mm"
include "uz3m2nn.mm"
include "nnne0d.mm"
include "clwwlknonel.mm"
include "syl.mm"
include "3ad2ant3.mm"
include "syl5bb.mm"
include "3simpa.mm"
include "adantr.mm"
include "simp32.mm"
include "anim12i.mm"
include "simpl33.mm"
include "3jca.mm"
include "3exp1.mm"
include "3adant3.mm"
include "com12.mm"
include "sylbid.mm"
include "imp32.mm"
include "numclwlk1lem2foalem.mm"
include "eleq1a.mm"
include "idd.mm"
include "3anim123d.mm"
include "mpd.mm"
include "extwwlkfabel.mm"
include "mpbir2and.mm"
include "ex.mm"

theorem numclwlk1lem2foa
  let vw: setvar w
  let vv: setvar v
  let cC: class C
  let vn: setvar n
  let cF: class F
  let cG: class G
  let cN: class N
  let cV: class V
  let cW: class W
  let cX: class X
  let cY: class Y
  let vi: setvar i
  assume extwwlkfab.v: |- V = ( Vtx ` G )
  assume extwwlkfab.c: |- C = ( v e. V , n e. ( ZZ>= ` 2 ) |-> { w e. ( n ClWWalksN G ) | ( ( w ` 0 ) = v /\ ( w ` ( n - 2 ) ) = ( w ` 0 ) ) } )
  assume extwwlkfab.f: |- F = ( X ( ClWWalksNOn ` G ) ( N - 2 ) )

  disjoint G n
  disjoint G v
  disjoint G w
  disjoint n v
  disjoint n w
  disjoint v w
  disjoint V n
  disjoint V v
  disjoint V w
  disjoint X n
  disjoint X v
  disjoint X w
  disjoint N n
  disjoint N v
  disjoint N w
  disjoint F w
  disjoint W w
  disjoint Y w
  disjoint G i
  disjoint W i
  assert |- ( ( G e. USGraph /\ X e. V /\ N e. ( ZZ>= ` 3 ) ) -> ( ( W e. F /\ Y e. ( G NeighbVtx X ) ) -> ( ( W ++ <" X "> ) ++ <" Y "> ) e. ( X C N ) ) )

  proof
    cG
    cusgr
    wcel
    #
    cX
    cV
    wcel
    #
    cN
    c3
    cuz
    cfv
    wcel
    #
    w3a
    #
    cW
    cF
    wcel
    #
    cY
    cG
    cX
    cnbgr
    co
    #
    wcel
    #
    wa
    #
    cW
    cX
    cs1
    cconcat
    co
    cY
    cs1
    cconcat
    co
    #
    cX
    cN
    cC
    co
    wcel
    #
    @3
    @7
    wa
    #
    @9
    @8
    cN
    cG
    cclwwlkn
    co
    wcel
    #
    @8
    cc0
    cN
    c2
    cmin
    co
    #
    cop
    csubstr
    co
    #
    cF
    wcel
    #
    cN
    c1
    cmin
    co
    @8
    cfv
    #
    @5
    wcel
    #
    @12
    @8
    cfv
    cX
    wceq
    #
    w3a
    #
    @10
    @1
    cY
    cV
    wcel
    #
    @2
    cX
    cY
    cpr
    cG
    cedg
    cfv
    #
    wcel
    #
    cW
    cX
    @12
    cG
    cclwwlknon
    cfv
    co
    #
    wcel
    #
    @11
    @0
    @1
    @2
    @7
    simpl2
    @6
    @19
    @3
    @4
    cG
    cX
    cY
    cV
    extwwlkfab.v
    nbgrisvtx
    #
    ad2antll
    @0
    @1
    @2
    @7
    simpl3
    @3
    @7
    @21
    @0
    @1
    @7
    @21
    wi
    @2
    @0
    @6
    @21
    @4
    @6
    cX
    cG
    cY
    cnbgr
    co
    wcel
    #
    @0
    @21
    cG
    cX
    cY
    nbgrsym
    @0
    @25
    @21
    @20
    cG
    cY
    cX
    @20
    eqid
    #
    nbusgreledg
    biimpd
    syl5bi
    adantld
    3ad2ant1
    imp
    @10
    cW
    cF
    @22
    @3
    @4
    @6
    simprl
    #
    extwwlkfab.f
    syl6eleq
    @20
    cG
    cN
    cV
    cW
    cX
    cY
    extwwlkfab.v
    @26
    clwwlknonex2
    syl311anc
    @10
    @13
    cW
    wceq
    #
    @15
    cY
    wceq
    #
    @17
    w3a
    #
    @18
    @10
    cW
    cV
    cword
    wcel
    #
    cW
    chash
    cfv
    #
    @12
    wceq
    #
    wa
    #
    @1
    @19
    wa
    #
    @2
    w3a
    #
    @30
    @3
    @4
    @6
    @36
    @3
    @4
    @31
    vi
    cv
    #
    cW
    cfv
    @37
    c1
    caddc
    co
    cW
    cfv
    cpr
    @20
    wcel
    vi
    cc0
    @32
    c1
    cmin
    co
    cfzo
    co
    wral
    #
    cW
    clsw
    cfv
    cc0
    cW
    cfv
    #
    cpr
    @20
    wcel
    #
    w3a
    #
    @33
    @39
    cX
    wceq
    #
    w3a
    #
    @6
    @36
    wi
    #
    @4
    @23
    @3
    @43
    cF
    @22
    cW
    extwwlkfab.f
    eleq2i
    @2
    @0
    @23
    @43
    wb
    #
    @1
    @2
    @12
    cc0
    wne
    @45
    @2
    @12
    cN
    uz3m2nn
    nnne0d
    vi
    @20
    cG
    @12
    cV
    cW
    cX
    extwwlkfab.v
    @26
    clwwlknonel
    syl
    3ad2ant3
    syl5bb
    @43
    @3
    @44
    @41
    @33
    @3
    @44
    wi
    #
    @42
    @41
    @33
    @46
    @31
    @38
    @33
    @46
    wi
    @40
    @31
    @33
    @3
    @6
    @36
    @31
    @33
    @3
    w3a
    #
    @6
    wa
    @34
    @35
    @2
    @47
    @34
    @6
    @31
    @33
    @3
    3simpa
    adantr
    @47
    @1
    @6
    @19
    @31
    @33
    @0
    @1
    @2
    simp32
    @24
    anim12i
    @0
    @1
    @2
    @31
    @33
    @6
    simpl33
    3jca
    3exp1
    3ad2ant1
    imp
    3adant3
    com12
    sylbid
    imp32
    cN
    cV
    cW
    cX
    cY
    numclwlk1lem2foalem
    syl
    @10
    @28
    @14
    @29
    @16
    @17
    @17
    @10
    @4
    @28
    @14
    wi
    @27
    cW
    cF
    @13
    eleq1a
    syl
    @6
    @29
    @16
    wi
    @3
    @4
    cY
    @5
    @15
    eleq1a
    ad2antll
    @10
    @17
    idd
    3anim123d
    mpd
    @3
    @9
    @11
    @18
    wa
    wb
    @7
    vw
    vv
    cC
    vn
    cF
    cG
    cN
    cV
    @8
    cX
    extwwlkfab.v
    extwwlkfab.c
    extwwlkfab.f
    extwwlkfabel
    adantr
    mpbir2and
    ex
end
