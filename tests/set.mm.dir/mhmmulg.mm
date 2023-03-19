include "cn0.mm"
include "wcel.mm"
include "cmhm.mm"
include "co.mm"
include "cfv.mm"
include "wceq.mm"
include "wa.mm"
include "cv.mm"
include "wi.mm"
include "cc0.mm"
include "c1.mm"
include "caddc.mm"
include "oveq1.mm"
include "fveq2d.mm"
include "eqeq12d.mm"
include "imbi2d.mm"
include "c0g.mm"
include "eqid.mm"
include "mhm0.mm"
include "adantr.mm"
include "mulg0.mm"
include "adantl.mm"
include "cbs.mm"
include "mhmf.mm"
include "ffvelrnda.mm"
include "syl.mm"
include "3eqtr4d.mm"
include "cplusg.mm"
include "cmnd.mm"
include "mhmrcl1.mm"
include "ad2antrr.mm"
include "simpr.mm"
include "simplr.mm"
include "mulgnn0p1.mm"
include "syl3anc.mm"
include "simpll.mm"
include "mulgnn0cl.mm"
include "an32s.mm"
include "mhmlin.mm"
include "eqtrd.mm"
include "mhmrcl2.mm"
include "syl5ibr.mm"
include "expcom.mm"
include "a2d.mm"
include "nn0ind.mm"
include "3impib.mm"
include "3com12.mm"

theorem mhmmulg
  let cB: class B
  let c.x: class .x.
  let c.xp: class .X.
  let cF: class F
  let cG: class G
  let cH: class H
  let cN: class N
  let cX: class X
  let vm: setvar m
  let vn: setvar n
  assume mhmmulg.b: |- B = ( Base ` G )
  assume mhmmulg.s: |- .x. = ( .g ` G )
  assume mhmmulg.t: |- .X. = ( .g ` H )


  assert |- ( ( F e. ( G MndHom H ) /\ N e. NN0 /\ X e. B ) -> ( F ` ( N .x. X ) ) = ( N .X. ( F ` X ) ) )

  proof
    cN
    cn0
    wcel
    #
    cF
    cG
    cH
    cmhm
    co
    wcel
    #
    cX
    cB
    wcel
    #
    cN
    cX
    c.x
    co
    #
    cF
    cfv
    #
    cN
    cX
    cF
    cfv
    #
    c.xp
    co
    #
    wceq
    #
    @0
    @1
    @2
    @7
    @1
    @2
    wa
    #
    vn
    cv
    #
    cX
    c.x
    co
    #
    cF
    cfv
    #
    @9
    @5
    c.xp
    co
    #
    wceq
    #
    wi
    @8
    cc0
    cX
    c.x
    co
    #
    cF
    cfv
    #
    cc0
    @5
    c.xp
    co
    #
    wceq
    #
    wi
    @8
    vm
    cv
    #
    cX
    c.x
    co
    #
    cF
    cfv
    #
    @18
    @5
    c.xp
    co
    #
    wceq
    #
    wi
    @8
    @18
    c1
    caddc
    co
    #
    cX
    c.x
    co
    #
    cF
    cfv
    #
    @23
    @5
    c.xp
    co
    #
    wceq
    #
    wi
    @8
    @7
    wi
    vn
    vm
    cN
    @9
    cc0
    wceq
    #
    @13
    @17
    @8
    @28
    @11
    @15
    @12
    @16
    @28
    @10
    @14
    cF
    @9
    cc0
    cX
    c.x
    oveq1
    fveq2d
    @9
    cc0
    @5
    c.xp
    oveq1
    eqeq12d
    imbi2d
    @9
    @18
    wceq
    #
    @13
    @22
    @8
    @29
    @11
    @20
    @12
    @21
    @29
    @10
    @19
    cF
    @9
    @18
    cX
    c.x
    oveq1
    fveq2d
    @9
    @18
    @5
    c.xp
    oveq1
    eqeq12d
    imbi2d
    @9
    @23
    wceq
    #
    @13
    @27
    @8
    @30
    @11
    @25
    @12
    @26
    @30
    @10
    @24
    cF
    @9
    @23
    cX
    c.x
    oveq1
    fveq2d
    @9
    @23
    @5
    c.xp
    oveq1
    eqeq12d
    imbi2d
    @9
    cN
    wceq
    #
    @13
    @7
    @8
    @31
    @11
    @4
    @12
    @6
    @31
    @10
    @3
    cF
    @9
    cN
    cX
    c.x
    oveq1
    fveq2d
    @9
    cN
    @5
    c.xp
    oveq1
    eqeq12d
    imbi2d
    @8
    cG
    c0g
    cfv
    #
    cF
    cfv
    #
    cH
    c0g
    cfv
    #
    @15
    @16
    @1
    @33
    @34
    wceq
    @2
    cG
    cH
    cF
    @34
    @32
    @32
    eqid
    #
    @34
    eqid
    #
    mhm0
    adantr
    @8
    @14
    @32
    cF
    @2
    @14
    @32
    wceq
    @1
    cB
    c.x
    cG
    cX
    @32
    mhmmulg.b
    @35
    mhmmulg.s
    mulg0
    adantl
    fveq2d
    @8
    @5
    cH
    cbs
    cfv
    #
    wcel
    #
    @16
    @34
    wceq
    @1
    cB
    @37
    cX
    cF
    cB
    @37
    cG
    cH
    cF
    mhmmulg.b
    @37
    eqid
    #
    mhmf
    ffvelrnda
    #
    @37
    c.xp
    cH
    @5
    @34
    @39
    @36
    mhmmulg.t
    mulg0
    syl
    3eqtr4d
    @18
    cn0
    wcel
    #
    @8
    @22
    @27
    @8
    @41
    @22
    @27
    wi
    @22
    @27
    @8
    @41
    wa
    #
    @20
    @5
    cH
    cplusg
    cfv
    #
    co
    #
    @21
    @5
    @43
    co
    #
    wceq
    @20
    @21
    @5
    @43
    oveq1
    @42
    @25
    @44
    @26
    @45
    @42
    @25
    @19
    cX
    cG
    cplusg
    cfv
    #
    co
    #
    cF
    cfv
    #
    @44
    @42
    @24
    @47
    cF
    @42
    cG
    cmnd
    wcel
    #
    @41
    @2
    @24
    @47
    wceq
    @1
    @49
    @2
    @41
    cG
    cH
    cF
    mhmrcl1
    #
    ad2antrr
    @8
    @41
    simpr
    #
    @1
    @2
    @41
    simplr
    #
    cB
    @46
    c.x
    cG
    @18
    cX
    mhmmulg.b
    mhmmulg.s
    @46
    eqid
    #
    mulgnn0p1
    syl3anc
    fveq2d
    @42
    @1
    @19
    cB
    wcel
    #
    @2
    @48
    @44
    wceq
    @1
    @2
    @41
    simpll
    @1
    @41
    @2
    @54
    @1
    @41
    wa
    #
    @2
    wa
    @49
    @41
    @2
    @54
    @1
    @49
    @41
    @2
    @50
    ad2antrr
    @1
    @41
    @2
    simplr
    @55
    @2
    simpr
    cB
    c.x
    cG
    @18
    cX
    mhmmulg.b
    mhmmulg.s
    mulgnn0cl
    syl3anc
    an32s
    @52
    cB
    @46
    @43
    cG
    cH
    cF
    @19
    cX
    mhmmulg.b
    @53
    @43
    eqid
    #
    mhmlin
    syl3anc
    eqtrd
    @42
    cH
    cmnd
    wcel
    #
    @41
    @38
    @26
    @45
    wceq
    @1
    @57
    @2
    @41
    cG
    cH
    cF
    mhmrcl2
    ad2antrr
    @51
    @8
    @38
    @41
    @40
    adantr
    @37
    @43
    c.xp
    cH
    @18
    @5
    @39
    mhmmulg.t
    @56
    mulgnn0p1
    syl3anc
    eqeq12d
    syl5ibr
    expcom
    a2d
    nn0ind
    3impib
    3com12
end
