include "cv.mm"
include "wceq.mm"
include "cur.mm"
include "cfv.mm"
include "cif.mm"
include "cmpt.mm"
include "cvsca.mm"
include "co.mm"
include "caddc.mm"
include "cof.mm"
include "casa.mm"
include "wcel.mm"
include "csca.mm"
include "cbs.mm"
include "ccrg.mm"
include "mplassa.mm"
include "syl2anc.mm"
include "mplsca.mm"
include "fveq2d.mm"
include "syl5eq.mm"
include "eleqtrd.mm"
include "eqid.mm"
include "crg.mm"
include "crngring.mm"
include "syl.mm"
include "mplmon.mm"
include "clmod.mm"
include "assalmod.mm"
include "lmodvscl.mm"
include "syl3anc.mm"
include "assaass.mm"
include "syl13anc.mm"
include "assaassr.mm"
include "oveq2d.mm"
include "cmulr.mm"
include "mplmonmul.mm"
include "psrbagaddcl.mm"
include "lmodvsass.mm"
include "syl5req.mm"
include "oveqd.mm"
include "oveq1d.mm"
include "3eqtr2d.mm"
include "3eqtrd.mm"
include "mplmon2.mm"
include "oveq12d.mm"
include "ringcl.mm"
include "3eqtr3d.mm"

theorem mplmon2mul
  let wph: wff ph
  let vy: setvar y
  let cC: class C
  let cD: class D
  let cP: class P
  let cR: class R
  let c.xb: class .xb
  let c.x: class .x.
  let vf: setvar f
  let cF: class F
  let cG: class G
  let cI: class I
  let cW: class W
  let cX: class X
  let cY: class Y
  let c.0: class .0.
  assume mplmon2cl.p: |- P = ( I mPoly R )
  assume mplmon2cl.d: |- D = { f e. ( NN0 ^m I ) | ( `' f " NN ) e. Fin }
  assume mplmon2cl.z: |- .0. = ( 0g ` R )
  assume mplmon2cl.c: |- C = ( Base ` R )
  assume mplmon2cl.i: |- ( ph -> I e. W )
  assume mplmon2mul.r: |- ( ph -> R e. CRing )
  assume mplmon2mul.t: |- .xb = ( .r ` P )
  assume mplmon2mul.u: |- .x. = ( .r ` R )
  assume mplmon2mul.x: |- ( ph -> X e. D )
  assume mplmon2mul.y: |- ( ph -> Y e. D )
  assume mplmon2mul.f: |- ( ph -> F e. C )
  assume mplmon2mul.g: |- ( ph -> G e. C )

  disjoint ph y
  disjoint C y
  disjoint D y
  disjoint F y
  disjoint G y
  disjoint I f
  disjoint R y
  disjoint .x. y
  disjoint X f
  disjoint X y
  disjoint f y
  disjoint Y f
  disjoint Y y
  disjoint .0. y
  assert |- ( ph -> ( ( y e. D |-> if ( y = X , F , .0. ) ) .xb ( y e. D |-> if ( y = Y , G , .0. ) ) ) = ( y e. D |-> if ( y = ( X oF + Y ) , ( F .x. G ) , .0. ) ) )

  proof
    wph
    cF
    vy
    cD
    vy
    cv
    #
    cX
    wceq
    #
    cR
    cur
    cfv
    #
    c.0
    cif
    cmpt
    #
    cP
    cvsca
    cfv
    #
    co
    #
    cG
    vy
    cD
    @0
    cY
    wceq
    #
    @2
    c.0
    cif
    cmpt
    #
    @4
    co
    #
    c.xb
    co
    #
    cF
    cG
    c.x
    co
    #
    vy
    cD
    @0
    cX
    cY
    caddc
    cof
    co
    #
    wceq
    #
    @2
    c.0
    cif
    cmpt
    #
    @4
    co
    #
    vy
    cD
    @1
    cF
    c.0
    cif
    cmpt
    #
    vy
    cD
    @6
    cG
    c.0
    cif
    cmpt
    #
    c.xb
    co
    vy
    cD
    @12
    @10
    c.0
    cif
    cmpt
    wph
    @9
    cF
    @3
    @8
    c.xb
    co
    #
    @4
    co
    #
    cF
    cG
    @3
    @7
    c.xb
    co
    #
    @4
    co
    #
    @4
    co
    #
    @14
    wph
    cP
    casa
    wcel
    #
    cF
    cP
    csca
    cfv
    #
    cbs
    cfv
    #
    wcel
    #
    @3
    cP
    cbs
    cfv
    #
    wcel
    #
    @8
    @26
    wcel
    #
    @9
    @18
    wceq
    wph
    cI
    cW
    wcel
    #
    cR
    ccrg
    wcel
    #
    @22
    mplmon2cl.i
    mplmon2mul.r
    cP
    cR
    cI
    cW
    mplmon2cl.p
    mplassa
    syl2anc
    #
    wph
    cF
    cC
    @24
    mplmon2mul.f
    wph
    cC
    cR
    cbs
    cfv
    @24
    mplmon2cl.c
    wph
    cR
    @23
    cbs
    wph
    cP
    cR
    cI
    cW
    ccrg
    mplmon2cl.p
    mplmon2cl.i
    mplmon2mul.r
    mplsca
    #
    fveq2d
    syl5eq
    #
    eleqtrd
    #
    wph
    vy
    @26
    cD
    cP
    cR
    @2
    vf
    cI
    cW
    cX
    c.0
    mplmon2cl.p
    @26
    eqid
    #
    mplmon2cl.z
    @2
    eqid
    #
    mplmon2cl.d
    mplmon2cl.i
    wph
    @30
    cR
    crg
    wcel
    #
    mplmon2mul.r
    cR
    crngring
    syl
    #
    mplmon2mul.x
    mplmon
    #
    wph
    cP
    clmod
    wcel
    #
    cG
    @24
    wcel
    #
    @7
    @26
    wcel
    #
    @28
    wph
    @22
    @40
    @31
    cP
    assalmod
    syl
    #
    wph
    cG
    cC
    @24
    mplmon2mul.g
    @33
    eleqtrd
    #
    wph
    vy
    @26
    cD
    cP
    cR
    @2
    vf
    cI
    cW
    cY
    c.0
    mplmon2cl.p
    @35
    mplmon2cl.z
    @36
    mplmon2cl.d
    mplmon2cl.i
    @38
    mplmon2mul.y
    mplmon
    #
    cG
    @4
    @23
    @24
    @26
    cP
    @7
    @35
    @23
    eqid
    #
    @4
    eqid
    #
    @24
    eqid
    #
    lmodvscl
    syl3anc
    cF
    @24
    @4
    c.xb
    @23
    @26
    cP
    @3
    @8
    @35
    @46
    @48
    @47
    mplmon2mul.t
    assaass
    syl13anc
    wph
    @17
    @20
    cF
    @4
    wph
    @22
    @41
    @27
    @42
    @17
    @20
    wceq
    @31
    @44
    @39
    @45
    cG
    @24
    @4
    c.xb
    @23
    @26
    cP
    @3
    @7
    @35
    @46
    @48
    @47
    mplmon2mul.t
    assaassr
    syl13anc
    oveq2d
    wph
    @21
    cF
    cG
    @13
    @4
    co
    #
    @4
    co
    #
    cF
    cG
    @23
    cmulr
    cfv
    #
    co
    #
    @13
    @4
    co
    #
    @14
    wph
    @20
    @49
    cF
    @4
    wph
    @19
    @13
    cG
    @4
    wph
    vy
    @26
    cD
    cP
    cR
    c.xb
    @2
    vf
    cI
    cW
    cX
    cY
    c.0
    mplmon2cl.p
    @35
    mplmon2cl.z
    @36
    mplmon2cl.d
    mplmon2cl.i
    @38
    mplmon2mul.x
    mplmon2mul.t
    mplmon2mul.y
    mplmonmul
    oveq2d
    oveq2d
    wph
    @40
    @25
    @41
    @13
    @26
    wcel
    @53
    @50
    wceq
    @43
    @34
    @44
    wph
    vy
    @26
    cD
    cP
    cR
    @2
    vf
    cI
    cW
    @11
    c.0
    mplmon2cl.p
    @35
    mplmon2cl.z
    @36
    mplmon2cl.d
    mplmon2cl.i
    @38
    wph
    @29
    cX
    cD
    wcel
    cY
    cD
    wcel
    @11
    cD
    wcel
    mplmon2cl.i
    mplmon2mul.x
    mplmon2mul.y
    cD
    vf
    cX
    cY
    cI
    cW
    mplmon2cl.d
    psrbagaddcl
    syl3anc
    #
    mplmon
    cF
    cG
    @4
    @51
    @23
    @24
    @26
    cP
    @13
    @35
    @46
    @47
    @48
    @51
    eqid
    lmodvsass
    syl13anc
    wph
    @52
    @10
    @13
    @4
    wph
    @51
    c.x
    cF
    cG
    wph
    c.x
    cR
    cmulr
    cfv
    @51
    mplmon2mul.u
    wph
    cR
    @23
    cmulr
    @32
    fveq2d
    syl5req
    oveqd
    oveq1d
    3eqtr2d
    3eqtrd
    wph
    @5
    @15
    @8
    @16
    c.xb
    wph
    vy
    cC
    cD
    cP
    cR
    @4
    @2
    vf
    cI
    cX
    cW
    cF
    c.0
    mplmon2cl.p
    @47
    mplmon2cl.d
    @36
    mplmon2cl.z
    mplmon2cl.c
    mplmon2cl.i
    @38
    mplmon2mul.x
    mplmon2mul.f
    mplmon2
    wph
    vy
    cC
    cD
    cP
    cR
    @4
    @2
    vf
    cI
    cY
    cW
    cG
    c.0
    mplmon2cl.p
    @47
    mplmon2cl.d
    @36
    mplmon2cl.z
    mplmon2cl.c
    mplmon2cl.i
    @38
    mplmon2mul.y
    mplmon2mul.g
    mplmon2
    oveq12d
    wph
    vy
    cC
    cD
    cP
    cR
    @4
    @2
    vf
    cI
    @11
    cW
    @10
    c.0
    mplmon2cl.p
    @47
    mplmon2cl.d
    @36
    mplmon2cl.z
    mplmon2cl.c
    mplmon2cl.i
    @38
    @54
    wph
    @37
    cF
    cC
    wcel
    cG
    cC
    wcel
    @10
    cC
    wcel
    @38
    mplmon2mul.f
    mplmon2mul.g
    cC
    cR
    c.x
    cF
    cG
    mplmon2cl.c
    mplmon2mul.u
    ringcl
    syl3anc
    mplmon2
    3eqtr3d
end
