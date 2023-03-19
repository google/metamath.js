include "crusgr.mm"
include "wbr.mm"
include "cfrgr.mm"
include "wcel.mm"
include "wa.mm"
include "cfn.mm"
include "c3.mm"
include "cuz.mm"
include "cfv.mm"
include "w3a.mm"
include "cclwwlknon.mm"
include "co.mm"
include "chash.mm"
include "cn.mm"
include "cc0.mm"
include "cv.mm"
include "wceq.mm"
include "c2.mm"
include "cmin.mm"
include "wne.mm"
include "cclwwlkn.mm"
include "crab.mm"
include "cmpt2.mm"
include "caddc.mm"
include "cexp.mm"
include "cmul.mm"
include "c1.mm"
include "cfusgr.mm"
include "simpl.mm"
include "simp1.mm"
include "finrusgrfusgr.mm"
include "syl2an.mm"
include "simpr2.mm"
include "uzuzle23.mm"
include "3ad2ant3.mm"
include "adantl.mm"
include "clsw.mm"
include "cwwlksn.mm"
include "eqid.mm"
include "numclwwlk3lem.mm"
include "syl21anc.mm"
include "numclwwlk2.mm"
include "anim12ci.mm"
include "3simpc.mm"
include "fveq1.mm"
include "eqeq1d.mm"
include "eqeq12d.mm"
include "anbi12d.mm"
include "cbvrabv.mm"
include "a1i.mm"
include "mpt2eq3ia.mm"
include "numclwwlk1.mm"
include "syl2anc.mm"
include "oveq12d.mm"
include "cc.mm"
include "c0.mm"
include "cn0.mm"
include "simpll.mm"
include "ne0i.mm"
include "3ad2ant2.mm"
include "frusgrnn0.mm"
include "syl3anc.mm"
include "nn0cnd.mm"
include "uz3m2nn.mm"
include "3anim3i.mm"
include "clwwlknonfin.mm"
include "3ad2ant1.mm"
include "hashcl.mm"
include "3syl.mm"
include "numclwlk3lem3.mm"
include "3eqtrd.mm"

theorem numclwwlk3
  let cG: class G
  let cK: class K
  let cN: class N
  let cV: class V
  let cX: class X
  let vn: setvar n
  let vu: setvar u
  let vv: setvar v
  let vw: setvar w
  assume numclwwlk3.v: |- V = ( Vtx ` G )


  assert |- ( ( ( G RegUSGraph K /\ G e. FriendGraph ) /\ ( V e. Fin /\ X e. V /\ N e. ( ZZ>= ` 3 ) ) ) -> ( # ` ( X ( ClWWalksNOn ` G ) N ) ) = ( ( ( K - 1 ) x. ( # ` ( X ( ClWWalksNOn ` G ) ( N - 2 ) ) ) ) + ( K ^ ( N - 2 ) ) ) )

  proof
    cG
    cK
    crusgr
    wbr
    #
    cG
    cfrgr
    wcel
    #
    wa
    #
    cV
    cfn
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
    wa
    #
    cX
    cN
    cG
    cclwwlknon
    cfv
    #
    co
    chash
    cfv
    #
    cX
    cN
    vv
    vn
    cV
    cn
    cc0
    vw
    cv
    #
    cfv
    #
    vv
    cv
    #
    wceq
    #
    vn
    cv
    #
    c2
    cmin
    co
    #
    @10
    cfv
    #
    @11
    wne
    wa
    vw
    @14
    cG
    cclwwlkn
    co
    #
    crab
    cmpt2
    #
    co
    chash
    cfv
    #
    cX
    cN
    vv
    vn
    cV
    c2
    cuz
    cfv
    #
    @13
    @16
    @11
    wceq
    #
    wa
    #
    vw
    @17
    crab
    #
    cmpt2
    #
    co
    chash
    cfv
    #
    caddc
    co
    #
    cK
    cN
    c2
    cmin
    co
    #
    cexp
    co
    #
    cX
    @27
    @8
    co
    #
    chash
    cfv
    #
    cmin
    co
    #
    cK
    @30
    cmul
    co
    #
    caddc
    co
    #
    cK
    c1
    cmin
    co
    @30
    cmul
    co
    @28
    caddc
    co
    #
    @7
    cG
    cfusgr
    wcel
    #
    @4
    cN
    @20
    wcel
    #
    @9
    @26
    wceq
    @2
    @0
    @3
    @35
    @6
    @0
    @1
    simpl
    #
    @3
    @4
    @5
    simp1
    #
    cG
    cK
    cV
    numclwwlk3.v
    finrusgrfusgr
    syl2an
    #
    @2
    @3
    @4
    @5
    simpr2
    @6
    @36
    @2
    @5
    @3
    @36
    @4
    cN
    uzuzle23
    3ad2ant3
    adantl
    #
    vw
    vv
    @24
    vv
    vn
    cV
    cn
    @13
    @10
    clsw
    cfv
    @12
    wne
    wa
    vw
    @14
    cG
    cwwlksn
    co
    crab
    cmpt2
    #
    vn
    cG
    @18
    cN
    cV
    cX
    numclwwlk3.v
    @41
    eqid
    #
    @18
    eqid
    #
    @24
    eqid
    numclwwlk3lem
    syl21anc
    @7
    @19
    @31
    @25
    @32
    caddc
    vw
    vv
    @41
    vn
    cG
    @18
    cK
    cN
    cV
    cX
    numclwwlk3.v
    @42
    @43
    numclwwlk2
    @7
    @3
    @0
    wa
    @4
    @5
    wa
    #
    @25
    @32
    wceq
    @2
    @0
    @6
    @3
    @37
    @38
    anim12ci
    @6
    @44
    @2
    @3
    @4
    @5
    3simpc
    adantl
    vu
    vv
    @24
    vn
    @29
    cG
    cK
    cN
    cV
    cX
    numclwwlk3.v
    vv
    vn
    cV
    @20
    @23
    cc0
    vu
    cv
    #
    cfv
    #
    @12
    wceq
    #
    @15
    @45
    cfv
    #
    @46
    wceq
    #
    wa
    #
    vu
    @17
    crab
    #
    @23
    @51
    wceq
    @12
    cV
    wcel
    @14
    @20
    wcel
    wa
    @22
    @50
    vw
    vu
    @17
    @10
    @45
    wceq
    #
    @13
    @47
    @21
    @49
    @52
    @11
    @46
    @12
    cc0
    @10
    @45
    fveq1
    #
    eqeq1d
    @52
    @16
    @48
    @11
    @46
    @15
    @10
    @45
    fveq1
    @53
    eqeq12d
    anbi12d
    cbvrabv
    a1i
    mpt2eq3ia
    @29
    eqid
    numclwwlk1
    syl2anc
    oveq12d
    @7
    cK
    cc
    wcel
    @30
    cc
    wcel
    #
    @36
    @33
    @34
    wceq
    @7
    cK
    @7
    @35
    @0
    cV
    c0
    wne
    #
    cK
    cn0
    wcel
    @39
    @0
    @1
    @6
    simpll
    @6
    @55
    @2
    @4
    @3
    @55
    @5
    cV
    cX
    ne0i
    3ad2ant2
    adantl
    cG
    cK
    cV
    numclwwlk3.v
    frusgrnn0
    syl3anc
    nn0cnd
    @7
    @3
    @4
    @27
    cn
    wcel
    #
    w3a
    #
    @29
    cfn
    wcel
    #
    @54
    @6
    @57
    @2
    @5
    @56
    @3
    @4
    cN
    uz3m2nn
    3anim3i
    adantl
    @3
    @4
    @58
    @56
    cG
    @27
    cV
    cX
    numclwwlk3.v
    clwwlknonfin
    3ad2ant1
    @58
    @30
    @29
    hashcl
    nn0cnd
    3syl
    @40
    cK
    cN
    @30
    numclwlk3lem3
    syl3anc
    3eqtrd
end
