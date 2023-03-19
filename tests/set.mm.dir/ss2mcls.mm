include "cmvh.mm"
include "cfv.mm"
include "crn.mm"
include "cun.mm"
include "cv.mm"
include "wss.mm"
include "cotp.mm"
include "cmax.mm"
include "wcel.mm"
include "cima.mm"
include "wbr.mm"
include "cmvrs.mm"
include "cxp.mm"
include "wi.mm"
include "wal.mm"
include "wa.mm"
include "cmsub.mm"
include "wral.mm"
include "cab.mm"
include "cint.mm"
include "co.mm"
include "unss1.mm"
include "sstr2.mm"
include "3syl.mm"
include "syl5com.mm"
include "imim2d.mm"
include "2alimdv.mm"
include "anim2d.mm"
include "imim1d.mm"
include "ralimdv.mm"
include "alimdv.mm"
include "anim12d.mm"
include "ss2abdv.mm"
include "intss.mm"
include "syl.mm"
include "sstrd.mm"
include "eqid.mm"
include "mclsval.mm"
include "3sstr4d.mm"

theorem ss2mcls
  let wph: wff ph
  let cB: class B
  let cC: class C
  let cD: class D
  let cT: class T
  let cE: class E
  let cK: class K
  let cX: class X
  let cY: class Y
  let vd: setvar d
  let vh: setvar h
  let vt: setvar t
  let vc: setvar c
  let vm: setvar m
  let vo: setvar o
  let vp: setvar p
  let vs: setvar s
  let vv: setvar v
  let va: setvar a
  let vb: setvar b
  let vx: setvar x
  let vz: setvar z
  let cH: class H
  let vy: setvar y
  let cL: class L
  let cA: class A
  let cO: class O
  let cS: class S
  let cM: class M
  let cP: class P
  let cQ: class Q
  let cV: class V
  let cW: class W
  assume mclsval.d: |- D = ( mDV ` T )
  assume mclsval.e: |- E = ( mEx ` T )
  assume mclsval.c: |- C = ( mCls ` T )
  assume mclsval.1: |- ( ph -> T e. mFS )
  assume mclsval.2: |- ( ph -> K C_ D )
  assume mclsval.3: |- ( ph -> B C_ E )
  assume ss2mcls.4: |- ( ph -> X C_ K )
  assume ss2mcls.5: |- ( ph -> Y C_ B )


  assert |- ( ph -> ( X C Y ) C_ ( K C B ) )

  proof
    wph
    cY
    cT
    cmvh
    cfv
    #
    crn
    #
    cun
    #
    vc
    cv
    #
    wss
    #
    vm
    cv
    #
    vo
    cv
    #
    vp
    cv
    #
    cotp
    cT
    cmax
    cfv
    #
    wcel
    #
    vs
    cv
    #
    @6
    @1
    cun
    cima
    @3
    wss
    #
    vx
    cv
    #
    vy
    cv
    #
    @5
    wbr
    #
    @12
    @0
    cfv
    @10
    cfv
    cT
    cmvrs
    cfv
    #
    cfv
    @13
    @0
    cfv
    @10
    cfv
    @15
    cfv
    cxp
    #
    cX
    wss
    #
    wi
    #
    vy
    wal
    vx
    wal
    #
    wa
    #
    @7
    @10
    cfv
    @3
    wcel
    #
    wi
    #
    vs
    cT
    cmsub
    cfv
    #
    crn
    #
    wral
    #
    wi
    #
    vp
    wal
    #
    vo
    wal
    vm
    wal
    #
    wa
    #
    vc
    cab
    #
    cint
    #
    cB
    @1
    cun
    #
    @3
    wss
    #
    @9
    @11
    @14
    @16
    cK
    wss
    #
    wi
    #
    vy
    wal
    vx
    wal
    #
    wa
    #
    @21
    wi
    #
    vs
    @24
    wral
    #
    wi
    #
    vp
    wal
    #
    vo
    wal
    vm
    wal
    #
    wa
    #
    vc
    cab
    #
    cint
    #
    cX
    cY
    cC
    co
    cK
    cB
    cC
    co
    wph
    @44
    @30
    wss
    @31
    @45
    wss
    wph
    @43
    @29
    vc
    wph
    @33
    @4
    @42
    @28
    wph
    cY
    cB
    wss
    @2
    @32
    wss
    @33
    @4
    wi
    ss2mcls.5
    cY
    cB
    @1
    unss1
    @2
    @32
    @3
    sstr2
    3syl
    wph
    @41
    @27
    vm
    vo
    wph
    @40
    @26
    vp
    wph
    @39
    @25
    @9
    wph
    @38
    @22
    vs
    @24
    wph
    @20
    @37
    @21
    wph
    @19
    @36
    @11
    wph
    @18
    @35
    vx
    vy
    wph
    @17
    @34
    @14
    wph
    cX
    cK
    wss
    @17
    @34
    ss2mcls.4
    @16
    cX
    cK
    sstr2
    syl5com
    imim2d
    2alimdv
    anim2d
    imim1d
    ralimdv
    imim2d
    alimdv
    2alimdv
    anim12d
    ss2abdv
    @44
    @30
    intss
    syl
    wph
    vx
    vy
    @8
    cY
    cC
    cD
    @23
    cT
    vm
    vo
    cE
    @0
    cX
    @15
    vs
    vp
    vc
    mclsval.d
    mclsval.e
    mclsval.c
    mclsval.1
    wph
    cX
    cK
    cD
    ss2mcls.4
    mclsval.2
    sstrd
    wph
    cY
    cB
    cE
    ss2mcls.5
    mclsval.3
    sstrd
    @0
    eqid
    #
    @8
    eqid
    #
    @23
    eqid
    #
    @15
    eqid
    #
    mclsval
    wph
    vx
    vy
    @8
    cB
    cC
    cD
    @23
    cT
    vm
    vo
    cE
    @0
    cK
    @15
    vs
    vp
    vc
    mclsval.d
    mclsval.e
    mclsval.c
    mclsval.1
    mclsval.2
    mclsval.3
    @46
    @47
    @48
    @49
    mclsval
    3sstr4d
end
