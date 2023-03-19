include "cn0.mm"
include "wcel.mm"
include "cv.mm"
include "wceq.mm"
include "cc0.mm"
include "cif.mm"
include "cmpt.mm"
include "cfv.mm"
include "co.mm"
include "wi.mm"
include "csn.mm"
include "cxp.mm"
include "c1.mm"
include "caddc.mm"
include "ifeq1.mm"
include "ifid.mm"
include "syl6eq.mm"
include "mpteq2dv.mm"
include "fconstmpt.mm"
include "syl6eqr.mm"
include "eqeq2d.mm"
include "ifbid.mm"
include "oveq1.mm"
include "eqeq12d.mm"
include "imbi2d.mm"
include "cur.mm"
include "cbs.mm"
include "eqid.mm"
include "mvrcl.mm"
include "mgpbas.mm"
include "ringidval.mm"
include "mulg0.mm"
include "syl.mm"
include "mpl1.mm"
include "eqtr2d.mm"
include "wa.mm"
include "cmulr.mm"
include "cof.mm"
include "adantr.mm"
include "crg.mm"
include "snifpsrbag.mm"
include "sylan.mm"
include "1nn0.mm"
include "a1i.mm"
include "syl2an.mm"
include "mplmonmul.mm"
include "mvrval.mm"
include "eqcomd.mm"
include "oveq2d.mm"
include "simplr.mm"
include "0nn0.mm"
include "ifcl.mm"
include "sylancl.mm"
include "keepel.mm"
include "eqidd.mm"
include "offval2.mm"
include "iftrue.mm"
include "oveq12d.mm"
include "eqtr4d.mm"
include "wn.mm"
include "00id.mm"
include "iffalse.mm"
include "3eqtr4a.mm"
include "pm2.61i.mm"
include "mpteq2i.mm"
include "3eqtr3rd.mm"
include "cmnd.mm"
include "mplring.mm"
include "syl2anc.mm"
include "ringmgp.mm"
include "simpr.mm"
include "mgpplusg.mm"
include "mulgnn0p1.mm"
include "syl3anc.mm"
include "syl5ibr.mm"
include "expcom.mm"
include "a2d.mm"
include "nn0ind.mm"
include "mpcom.mm"

theorem mplcoe3
  let wph: wff ph
  let vy: setvar y
  let cD: class D
  let cP: class P
  let cR: class R
  let c.1: class .1.
  let vf: setvar f
  let vk: setvar k
  let c.ex: class .^
  let cG: class G
  let cI: class I
  let cN: class N
  let cV: class V
  let cW: class W
  let cX: class X
  let c.0: class .0.
  let vi: setvar i
  let vn: setvar n
  let vw: setvar w
  let vx: setvar x
  let vz: setvar z
  let cB: class B
  let cY: class Y
  let c.x: class .x.
  assume mplcoe1.p: |- P = ( I mPoly R )
  assume mplcoe1.d: |- D = { f e. ( NN0 ^m I ) | ( `' f " NN ) e. Fin }
  assume mplcoe1.z: |- .0. = ( 0g ` R )
  assume mplcoe1.o: |- .1. = ( 1r ` R )
  assume mplcoe1.i: |- ( ph -> I e. W )
  assume mplcoe2.g: |- G = ( mulGrp ` P )
  assume mplcoe2.m: |- .^ = ( .g ` G )
  assume mplcoe2.v: |- V = ( I mVar R )
  assume mplcoe3.r: |- ( ph -> R e. Ring )
  assume mplcoe3.x: |- ( ph -> X e. I )
  assume mplcoe3.n: |- ( ph -> N e. NN0 )

  disjoint .^ k
  disjoint k y
  disjoint .1. k
  disjoint .1. y
  disjoint G k
  disjoint f k
  disjoint f y
  disjoint I f
  disjoint I k
  disjoint I y
  disjoint N k
  disjoint N y
  disjoint k ph
  disjoint ph y
  disjoint R f
  disjoint R y
  disjoint D k
  disjoint D y
  disjoint P k
  disjoint V k
  disjoint .0. f
  disjoint .0. k
  disjoint .0. y
  disjoint X f
  disjoint X k
  disjoint X y
  disjoint W k
  disjoint W y
  disjoint i k
  disjoint i n
  disjoint i w
  disjoint i x
  disjoint i z
  disjoint .^ i
  disjoint k n
  disjoint k w
  disjoint k x
  disjoint k z
  disjoint n w
  disjoint n x
  disjoint n z
  disjoint .^ n
  disjoint w x
  disjoint w z
  disjoint .^ w
  disjoint x z
  disjoint .^ x
  disjoint .^ z
  disjoint i y
  disjoint .1. i
  disjoint n y
  disjoint .1. n
  disjoint w y
  disjoint .1. w
  disjoint x y
  disjoint .1. x
  disjoint y z
  disjoint .1. z
  disjoint B k
  disjoint G i
  disjoint G w
  disjoint G x
  disjoint G z
  disjoint f i
  disjoint f n
  disjoint f w
  disjoint f x
  disjoint f z
  disjoint I i
  disjoint I n
  disjoint I w
  disjoint I x
  disjoint I z
  disjoint N x
  disjoint i ph
  disjoint n ph
  disjoint ph w
  disjoint ph x
  disjoint ph z
  disjoint D i
  disjoint D n
  disjoint D w
  disjoint D x
  disjoint D z
  disjoint P i
  disjoint P w
  disjoint P x
  disjoint P z
  disjoint V i
  disjoint V n
  disjoint V w
  disjoint V x
  disjoint V z
  disjoint .0. i
  disjoint .0. n
  disjoint .0. w
  disjoint .0. x
  disjoint .0. z
  disjoint X n
  disjoint X w
  disjoint X x
  disjoint X z
  disjoint Y f
  disjoint Y i
  disjoint Y k
  disjoint Y w
  disjoint Y x
  disjoint Y y
  disjoint Y z
  disjoint W i
  disjoint .x. k
  disjoint .x. w
  disjoint .x. x
  disjoint .x. z
  assert |- ( ph -> ( y e. D |-> if ( y = ( k e. I |-> if ( k = X , N , 0 ) ) , .1. , .0. ) ) = ( N .^ ( V ` X ) ) )

  proof
    cN
    cn0
    wcel
    wph
    vy
    cD
    vy
    cv
    #
    vk
    cI
    vk
    cv
    #
    cX
    wceq
    #
    cN
    cc0
    cif
    #
    cmpt
    #
    wceq
    #
    c.1
    c.0
    cif
    #
    cmpt
    #
    cN
    cX
    cV
    cfv
    #
    c.ex
    co
    #
    wceq
    #
    mplcoe3.n
    wph
    vy
    cD
    @0
    vk
    cI
    @2
    vx
    cv
    #
    cc0
    cif
    #
    cmpt
    #
    wceq
    #
    c.1
    c.0
    cif
    #
    cmpt
    #
    @11
    @8
    c.ex
    co
    #
    wceq
    #
    wi
    wph
    vy
    cD
    @0
    cI
    cc0
    csn
    cxp
    #
    wceq
    #
    c.1
    c.0
    cif
    #
    cmpt
    #
    cc0
    @8
    c.ex
    co
    #
    wceq
    #
    wi
    wph
    vy
    cD
    @0
    vk
    cI
    @2
    vn
    cv
    #
    cc0
    cif
    #
    cmpt
    #
    wceq
    #
    c.1
    c.0
    cif
    #
    cmpt
    #
    @25
    @8
    c.ex
    co
    #
    wceq
    #
    wi
    wph
    vy
    cD
    @0
    vk
    cI
    @2
    @25
    c1
    caddc
    co
    #
    cc0
    cif
    #
    cmpt
    #
    wceq
    #
    c.1
    c.0
    cif
    #
    cmpt
    #
    @33
    @8
    c.ex
    co
    #
    wceq
    #
    wi
    wph
    @10
    wi
    vx
    vn
    cN
    @11
    cc0
    wceq
    #
    @18
    @24
    wph
    @41
    @16
    @22
    @17
    @23
    @41
    vy
    cD
    @15
    @21
    @41
    @14
    @20
    c.1
    c.0
    @41
    @13
    @19
    @0
    @41
    @13
    vk
    cI
    cc0
    cmpt
    @19
    @41
    vk
    cI
    @12
    cc0
    @41
    @12
    @2
    cc0
    cc0
    cif
    cc0
    @2
    @11
    cc0
    cc0
    ifeq1
    @2
    cc0
    ifid
    syl6eq
    mpteq2dv
    vk
    cI
    cc0
    fconstmpt
    syl6eqr
    eqeq2d
    ifbid
    mpteq2dv
    @11
    cc0
    @8
    c.ex
    oveq1
    eqeq12d
    imbi2d
    @11
    @25
    wceq
    #
    @18
    @32
    wph
    @42
    @16
    @30
    @17
    @31
    @42
    vy
    cD
    @15
    @29
    @42
    @14
    @28
    c.1
    c.0
    @42
    @13
    @27
    @0
    @42
    vk
    cI
    @12
    @26
    @2
    @11
    @25
    cc0
    ifeq1
    mpteq2dv
    eqeq2d
    ifbid
    mpteq2dv
    @11
    @25
    @8
    c.ex
    oveq1
    eqeq12d
    imbi2d
    @11
    @33
    wceq
    #
    @18
    @40
    wph
    @43
    @16
    @38
    @17
    @39
    @43
    vy
    cD
    @15
    @37
    @43
    @14
    @36
    c.1
    c.0
    @43
    @13
    @35
    @0
    @43
    vk
    cI
    @12
    @34
    @2
    @11
    @33
    cc0
    ifeq1
    mpteq2dv
    eqeq2d
    ifbid
    mpteq2dv
    @11
    @33
    @8
    c.ex
    oveq1
    eqeq12d
    imbi2d
    @11
    cN
    wceq
    #
    @18
    @10
    wph
    @44
    @16
    @7
    @17
    @9
    @44
    vy
    cD
    @15
    @6
    @44
    @14
    @5
    c.1
    c.0
    @44
    @13
    @4
    @0
    @44
    vk
    cI
    @12
    @3
    @2
    @11
    cN
    cc0
    ifeq1
    mpteq2dv
    eqeq2d
    ifbid
    mpteq2dv
    @11
    cN
    @8
    c.ex
    oveq1
    eqeq12d
    imbi2d
    wph
    @23
    cP
    cur
    cfv
    #
    @22
    wph
    @8
    cP
    cbs
    cfv
    #
    wcel
    #
    @23
    @45
    wceq
    wph
    @46
    cP
    cR
    cI
    cV
    cW
    cX
    mplcoe1.p
    mplcoe2.v
    @46
    eqid
    #
    mplcoe1.i
    mplcoe3.r
    mplcoe3.x
    mvrcl
    #
    @46
    c.ex
    cG
    @8
    @45
    @46
    cP
    cG
    mplcoe2.g
    @48
    mgpbas
    #
    cP
    @45
    cG
    mplcoe2.g
    @45
    eqid
    #
    ringidval
    mplcoe2.m
    mulg0
    syl
    wph
    vy
    cD
    cP
    cR
    @45
    c.1
    vf
    cI
    cW
    c.0
    mplcoe1.p
    mplcoe1.d
    mplcoe1.z
    mplcoe1.o
    @51
    mplcoe1.i
    mplcoe3.r
    mpl1
    eqtr2d
    @25
    cn0
    wcel
    #
    wph
    @32
    @40
    wph
    @52
    @32
    @40
    wi
    @32
    @40
    wph
    @52
    wa
    #
    @30
    @8
    cP
    cmulr
    cfv
    #
    co
    #
    @31
    @8
    @54
    co
    #
    wceq
    @30
    @31
    @8
    @54
    oveq1
    @53
    @38
    @55
    @39
    @56
    @53
    @30
    vy
    cD
    @0
    vk
    cI
    @2
    c1
    cc0
    cif
    #
    cmpt
    #
    wceq
    c.1
    c.0
    cif
    cmpt
    #
    @54
    co
    vy
    cD
    @0
    @27
    @58
    caddc
    cof
    co
    #
    wceq
    #
    c.1
    c.0
    cif
    #
    cmpt
    @55
    @38
    @53
    vy
    @46
    cD
    cP
    cR
    @54
    c.1
    vf
    cI
    cW
    @27
    @58
    c.0
    mplcoe1.p
    @48
    mplcoe1.z
    mplcoe1.o
    mplcoe1.d
    wph
    cI
    cW
    wcel
    #
    @52
    mplcoe1.i
    adantr
    #
    wph
    cR
    crg
    wcel
    #
    @52
    mplcoe3.r
    adantr
    #
    wph
    @63
    @52
    @27
    cD
    wcel
    mplcoe1.i
    vk
    cD
    vf
    cI
    @25
    cW
    cX
    mplcoe1.d
    snifpsrbag
    sylan
    @54
    eqid
    #
    wph
    @63
    c1
    cn0
    wcel
    #
    @58
    cD
    wcel
    @52
    mplcoe1.i
    @68
    @52
    1nn0
    a1i
    vk
    cD
    vf
    cI
    c1
    cW
    cX
    mplcoe1.d
    snifpsrbag
    syl2an
    mplmonmul
    @53
    @59
    @8
    @30
    @54
    @53
    @8
    @59
    @53
    vk
    cD
    cR
    c.1
    vy
    vf
    cI
    cV
    cW
    cX
    crg
    c.0
    mplcoe2.v
    mplcoe1.d
    mplcoe1.z
    mplcoe1.o
    @64
    @66
    wph
    cX
    cI
    wcel
    @52
    mplcoe3.x
    adantr
    mvrval
    eqcomd
    oveq2d
    @53
    vy
    cD
    @62
    @37
    @53
    @61
    @36
    c.1
    c.0
    @53
    @60
    @35
    @0
    @53
    @60
    vk
    cI
    @26
    @57
    caddc
    co
    #
    cmpt
    @35
    @53
    vk
    cI
    @26
    @57
    caddc
    @27
    @58
    cW
    cn0
    cn0
    @64
    @53
    @1
    cI
    wcel
    #
    wa
    #
    @52
    cc0
    cn0
    wcel
    @26
    cn0
    wcel
    wph
    @52
    @70
    simplr
    0nn0
    @2
    @25
    cc0
    cn0
    ifcl
    sylancl
    @57
    cn0
    wcel
    @71
    @2
    c1
    cc0
    cn0
    1nn0
    0nn0
    keepel
    a1i
    @53
    @27
    eqidd
    @53
    @58
    eqidd
    offval2
    vk
    cI
    @69
    @34
    @2
    @69
    @34
    wceq
    @2
    @69
    @33
    @34
    @2
    @26
    @25
    @57
    c1
    caddc
    @2
    @25
    cc0
    iftrue
    @2
    c1
    cc0
    iftrue
    oveq12d
    @2
    @33
    cc0
    iftrue
    eqtr4d
    @2
    wn
    #
    cc0
    cc0
    caddc
    co
    cc0
    @69
    @34
    00id
    @72
    @26
    cc0
    @57
    cc0
    caddc
    @2
    @25
    cc0
    iffalse
    @2
    c1
    cc0
    iffalse
    oveq12d
    @2
    @33
    cc0
    iffalse
    3eqtr4a
    pm2.61i
    mpteq2i
    syl6eq
    eqeq2d
    ifbid
    mpteq2dv
    3eqtr3rd
    @53
    cG
    cmnd
    wcel
    #
    @52
    @47
    @39
    @56
    wceq
    wph
    @73
    @52
    wph
    cP
    crg
    wcel
    #
    @73
    wph
    @63
    @65
    @74
    mplcoe1.i
    mplcoe3.r
    cP
    cR
    cI
    cW
    mplcoe1.p
    mplring
    syl2anc
    cP
    cG
    mplcoe2.g
    ringmgp
    syl
    adantr
    wph
    @52
    simpr
    wph
    @47
    @52
    @49
    adantr
    @46
    @54
    c.ex
    cG
    @25
    @8
    @50
    mplcoe2.m
    cP
    @54
    cG
    mplcoe2.g
    @67
    mgpplusg
    mulgnn0p1
    syl3anc
    eqeq12d
    syl5ibr
    expcom
    a2d
    nn0ind
    mpcom
end
