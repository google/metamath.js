include "cpw.mm"
include "wcel.mm"
include "clmod.mm"
include "w3a.mm"
include "cmap.mm"
include "co.mm"
include "cfv.mm"
include "cfsupp.mm"
include "wbr.mm"
include "wa.mm"
include "csn.mm"
include "cdif.mm"
include "cres.mm"
include "clinc.mm"
include "cv.mm"
include "cvsca.mm"
include "cmpt.mm"
include "cgsu.mm"
include "csca.mm"
include "cbs.mm"
include "wceq.mm"
include "simpl2.mm"
include "wss.mm"
include "fveq2i.mm"
include "eqtri.mm"
include "oveq1i.mm"
include "eleq2i.mm"
include "biimpi.mm"
include "3ad2ant1.mm"
include "adantl.mm"
include "difssd.mm"
include "elmapssres.mm"
include "syl2anc.mm"
include "elpwi.mm"
include "ssdifssd.mm"
include "cvv.mm"
include "wb.mm"
include "difexg.mm"
include "elpwg.mm"
include "syl.mm"
include "mpbird.mm"
include "pweqi.mm"
include "eleq2s.mm"
include "adantr.mm"
include "lincval.mm"
include "syl3anc.mm"
include "simpll.mm"
include "simplr1.mm"
include "simplr2.mm"
include "simpr.mm"
include "lincresunit3lem1.mm"
include "syl13anc.mm"
include "fvres.mm"
include "eqcomd.mm"
include "oveq1d.mm"
include "eqtrd.mm"
include "mpteq2dva.mm"
include "oveq2d.mm"
include "cplusg.mm"
include "eqid.mm"
include "cgrp.mm"
include "lmodfgrp.mm"
include "3ad2ant2.mm"
include "wf.mm"
include "elmapi.mm"
include "wi.mm"
include "ffvelrn.mm"
include "expcom.mm"
include "3ad2ant3.mm"
include "syl5com.mm"
include "impcom.mm"
include "grpinvcl.mm"
include "3ad2antr1.mm"
include "lincresunit1.mm"
include "3adantr3.mm"
include "ex.mm"
include "3syl.mm"
include "imp.mm"
include "eldifi.mm"
include "ssel2.mm"
include "lmodvscl.mm"
include "c0g.mm"
include "simp2.mm"
include "jca.mm"
include "lincresunit2.mm"
include "syl6breq.mm"
include "scmfsupp.mm"
include "syl6breqr.mm"
include "gsumvsmul.mm"
include "3eqtr2rd.mm"

theorem lincresunit3lem2
  let vz: setvar z
  let cB: class B
  let cR: class R
  let cS: class S
  let c.x: class .x.
  let cU: class U
  let cE: class E
  let cF: class F
  let cG: class G
  let cI: class I
  let cM: class M
  let cN: class N
  let cX: class X
  let c.0: class .0.
  let cZ: class Z
  let vs: setvar s
  let vk: setvar k
  let vx: setvar x
  assume lincresunit.b: |- B = ( Base ` M )
  assume lincresunit.r: |- R = ( Scalar ` M )
  assume lincresunit.e: |- E = ( Base ` R )
  assume lincresunit.u: |- U = ( Unit ` R )
  assume lincresunit.0: |- .0. = ( 0g ` R )
  assume lincresunit.z: |- Z = ( 0g ` M )
  assume lincresunit.n: |- N = ( invg ` R )
  assume lincresunit.i: |- I = ( invr ` R )
  assume lincresunit.t: |- .x. = ( .r ` R )
  assume lincresunit.g: |- G = ( s e. ( S \ { X } ) |-> ( ( I ` ( N ` ( F ` X ) ) ) .x. ( F ` s ) ) )

  disjoint B s
  disjoint E s
  disjoint F s
  disjoint M s
  disjoint S s
  disjoint X s
  disjoint U s
  disjoint I s
  disjoint N s
  disjoint .x. s
  disjoint s z
  disjoint B z
  disjoint E z
  disjoint F z
  disjoint G z
  disjoint M z
  disjoint N z
  disjoint R z
  disjoint S z
  disjoint U z
  disjoint X z
  disjoint Z z
  disjoint .0. s
  disjoint .0. z
  disjoint k x
  assert |- ( ( ( S e. ~P B /\ M e. LMod /\ X e. S ) /\ ( F e. ( E ^m S ) /\ ( F ` X ) e. U /\ F finSupp .0. ) ) -> ( ( N ` ( F ` X ) ) ( .s ` M ) ( M gsum ( z e. ( S \ { X } ) |-> ( ( G ` z ) ( .s ` M ) z ) ) ) ) = ( ( F |` ( S \ { X } ) ) ( linC ` M ) ( S \ { X } ) ) )

  proof
    cS
    cB
    cpw
    #
    wcel
    #
    cM
    clmod
    wcel
    #
    cX
    cS
    wcel
    #
    w3a
    #
    cF
    cE
    cS
    cmap
    co
    #
    wcel
    #
    cX
    cF
    cfv
    #
    cU
    wcel
    #
    cF
    c.0
    cfsupp
    wbr
    #
    w3a
    #
    wa
    #
    cF
    cS
    cX
    csn
    #
    cdif
    #
    cres
    #
    @13
    cM
    clinc
    cfv
    co
    #
    cM
    vz
    @13
    vz
    cv
    #
    @14
    cfv
    #
    @16
    cM
    cvsca
    cfv
    #
    co
    #
    cmpt
    #
    cgsu
    co
    #
    cM
    vz
    @13
    @7
    cN
    cfv
    #
    @16
    cG
    cfv
    #
    @16
    @18
    co
    #
    @18
    co
    #
    cmpt
    #
    cgsu
    co
    @22
    cM
    vz
    @13
    @24
    cmpt
    #
    cgsu
    co
    @18
    co
    @11
    @2
    @14
    cM
    csca
    cfv
    #
    cbs
    cfv
    #
    @13
    cmap
    co
    wcel
    #
    @13
    cM
    cbs
    cfv
    #
    cpw
    #
    wcel
    #
    @15
    @21
    wceq
    @1
    @2
    @3
    @10
    simpl2
    #
    @11
    cF
    @29
    cS
    cmap
    co
    #
    wcel
    #
    @13
    cS
    wss
    @30
    @10
    @36
    @4
    @6
    @8
    @36
    @9
    @6
    @36
    @5
    @35
    cF
    cE
    @29
    cS
    cmap
    cE
    cR
    cbs
    cfv
    @29
    lincresunit.e
    cR
    @28
    cbs
    lincresunit.r
    fveq2i
    eqtri
    oveq1i
    eleq2i
    biimpi
    3ad2ant1
    adantl
    @11
    cS
    @12
    difssd
    cF
    @29
    cS
    @13
    elmapssres
    syl2anc
    @4
    @33
    @10
    @1
    @2
    @33
    @3
    @33
    cS
    @32
    @0
    cS
    @32
    wcel
    #
    @33
    @13
    @31
    wss
    #
    @37
    cS
    @31
    @12
    cS
    @31
    elpwi
    ssdifssd
    @37
    @13
    cvv
    wcel
    #
    @33
    @38
    wb
    cS
    @12
    @32
    difexg
    @13
    @31
    cvv
    elpwg
    syl
    mpbird
    cB
    @31
    lincresunit.b
    pweqi
    eleq2s
    3ad2ant1
    #
    adantr
    vz
    @14
    cM
    @13
    clmod
    lincval
    syl3anc
    @11
    @26
    @20
    cM
    cgsu
    @11
    vz
    @13
    @25
    @19
    @11
    @16
    @13
    wcel
    #
    wa
    #
    @25
    @16
    cF
    cfv
    #
    @16
    @18
    co
    #
    @19
    @42
    @4
    @6
    @8
    @41
    @25
    @44
    wceq
    @4
    @10
    @41
    simpll
    @6
    @8
    @9
    @4
    @41
    simplr1
    @6
    @8
    @9
    @4
    @41
    simplr2
    @11
    @41
    simpr
    vz
    cB
    cR
    cS
    c.x
    cU
    cE
    cF
    cG
    cI
    cM
    cN
    cX
    c.0
    cZ
    vs
    lincresunit.b
    lincresunit.r
    lincresunit.e
    lincresunit.u
    lincresunit.0
    lincresunit.z
    lincresunit.n
    lincresunit.i
    lincresunit.t
    lincresunit.g
    lincresunit3lem1
    syl13anc
    @42
    @43
    @17
    @16
    @18
    @42
    @17
    @43
    @41
    @17
    @43
    wceq
    @11
    @16
    @13
    cF
    fvres
    adantl
    eqcomd
    oveq1d
    eqtrd
    mpteq2dva
    oveq2d
    @11
    @13
    cB
    cM
    cplusg
    cfv
    #
    cM
    cR
    @18
    vz
    cE
    cvv
    @22
    @24
    cZ
    lincresunit.b
    lincresunit.r
    lincresunit.e
    lincresunit.z
    @45
    eqid
    @18
    eqid
    #
    @34
    @4
    @39
    @10
    @1
    @2
    @39
    @3
    cS
    @12
    @0
    difexg
    3ad2ant1
    adantr
    @4
    @8
    @6
    @22
    cE
    wcel
    #
    @9
    @4
    @6
    wa
    cR
    cgrp
    wcel
    #
    @7
    cE
    wcel
    #
    @47
    @4
    @48
    @6
    @2
    @1
    @48
    @3
    cR
    cM
    lincresunit.r
    lmodfgrp
    3ad2ant2
    adantr
    @6
    @4
    @49
    @6
    cS
    cE
    cF
    wf
    #
    @4
    @49
    cF
    cE
    cS
    elmapi
    @3
    @1
    @50
    @49
    wi
    @2
    @50
    @3
    @49
    cS
    cE
    cX
    cF
    ffvelrn
    expcom
    3ad2ant3
    syl5com
    impcom
    cE
    cR
    cN
    @7
    lincresunit.e
    lincresunit.n
    grpinvcl
    syl2anc
    3ad2antr1
    @42
    @2
    @23
    cE
    wcel
    #
    @16
    cB
    wcel
    #
    @24
    cB
    wcel
    @11
    @2
    @41
    @34
    adantr
    @11
    @41
    @51
    @11
    cG
    cE
    @13
    cmap
    co
    wcel
    #
    @13
    cE
    cG
    wf
    #
    @41
    @51
    wi
    @4
    @6
    @8
    @53
    @9
    cB
    cR
    cS
    c.x
    cU
    cE
    cF
    cG
    cI
    cM
    cN
    cX
    c.0
    cZ
    vs
    lincresunit.b
    lincresunit.r
    lincresunit.e
    lincresunit.u
    lincresunit.0
    lincresunit.z
    lincresunit.n
    lincresunit.i
    lincresunit.t
    lincresunit.g
    lincresunit1
    3adantr3
    #
    cG
    cE
    @13
    elmapi
    @54
    @41
    @51
    @13
    cE
    @16
    cG
    ffvelrn
    ex
    3syl
    imp
    @11
    @41
    @52
    @4
    @41
    @52
    wi
    #
    @10
    @1
    @2
    @56
    @3
    @1
    cS
    cB
    wss
    #
    @41
    @52
    cS
    cB
    elpwi
    @41
    @16
    cS
    wcel
    #
    @57
    @52
    wi
    @16
    cS
    @12
    eldifi
    @57
    @58
    @52
    cS
    cB
    @16
    ssel2
    expcom
    syl
    syl5com
    3ad2ant1
    adantr
    imp
    @23
    @18
    cR
    cE
    cB
    cM
    @16
    lincresunit.b
    lincresunit.r
    @46
    lincresunit.e
    lmodvscl
    syl3anc
    @11
    @2
    @33
    wa
    #
    @53
    cG
    cR
    c0g
    cfv
    #
    cfsupp
    wbr
    #
    @27
    cZ
    cfsupp
    wbr
    @4
    @59
    @10
    @4
    @2
    @33
    @1
    @2
    @3
    simp2
    @40
    jca
    adantr
    @55
    @11
    cG
    c.0
    @60
    cfsupp
    cB
    cR
    cS
    c.x
    cU
    cE
    cF
    cG
    cI
    cM
    cN
    cX
    c.0
    cZ
    vs
    lincresunit.b
    lincresunit.r
    lincresunit.e
    lincresunit.u
    lincresunit.0
    lincresunit.z
    lincresunit.n
    lincresunit.i
    lincresunit.t
    lincresunit.g
    lincresunit2
    lincresunit.0
    syl6breq
    @59
    @53
    @61
    w3a
    @27
    cM
    c0g
    cfv
    cZ
    cfsupp
    vz
    cG
    cE
    cR
    cM
    @13
    lincresunit.r
    lincresunit.e
    scmfsupp
    lincresunit.z
    syl6breqr
    syl3anc
    gsumvsmul
    3eqtr2rd
end
