include "cuni.mm"
include "wcel.mm"
include "cv.mm"
include "wss.mm"
include "cfv.mm"
include "wi.mm"
include "wal.mm"
include "wral.mm"
include "dfss3.mm"
include "sylib.mm"
include "cvv.mm"
include "vex.mm"
include "a1i.mm"
include "setrec1lem1.mm"
include "ralbidv.mm"
include "mpbid.mm"
include "ralcom4.mm"
include "nfra1.mm"
include "nfv.mm"
include "rsp.mm"
include "elssuni.mm"
include "sstr2.mm"
include "syl5com.mm"
include "imim1d.mm"
include "alimdv.mm"
include "sylcom.mm"
include "com23.mm"
include "ralrimd.mm"
include "alimi.mm"
include "syl.mm"
include "unissb.mm"
include "imbi2i.mm"
include "albii.mm"
include "sylibr.mm"
include "uniexg.mm"
include "mpbird.mm"

theorem setrec1lem2
  let wph: wff ph
  let vy: setvar y
  let vz: setvar z
  let vw: setvar w
  let cF: class F
  let cV: class V
  let cX: class X
  let cY: class Y
  let vx: setvar x
  let vk: setvar k
  assume setrec1lem2.1: |- Y = { y | A. z ( A. w ( w C_ y -> ( w C_ z -> ( F ` w ) C_ z ) ) -> y C_ z ) }
  assume setrec1lem2.2: |- ( ph -> X e. V )
  assume setrec1lem2.3: |- ( ph -> X C_ Y )

  disjoint F y
  disjoint X w
  disjoint X y
  disjoint w y
  disjoint X z
  disjoint y z
  disjoint F x
  disjoint x y
  disjoint X x
  disjoint w x
  disjoint x z
  disjoint Y x
  disjoint ph x
  disjoint k x
  assert |- ( ph -> U. X e. Y )

  proof
    wph
    cX
    cuni
    #
    cY
    wcel
    vw
    cv
    #
    @0
    wss
    #
    @1
    vz
    cv
    #
    wss
    @1
    cF
    cfv
    @3
    wss
    wi
    #
    wi
    #
    vw
    wal
    #
    @0
    @3
    wss
    #
    wi
    #
    vz
    wal
    #
    wph
    @6
    vx
    cv
    #
    @3
    wss
    #
    vx
    cX
    wral
    #
    wi
    #
    vz
    wal
    #
    @9
    wph
    @1
    @10
    wss
    #
    @4
    wi
    #
    vw
    wal
    #
    @11
    wi
    #
    vx
    cX
    wral
    #
    vz
    wal
    #
    @14
    wph
    @18
    vz
    wal
    #
    vx
    cX
    wral
    #
    @20
    wph
    @10
    cY
    wcel
    #
    vx
    cX
    wral
    #
    @22
    wph
    cX
    cY
    wss
    @24
    setrec1lem2.3
    vx
    cX
    cY
    dfss3
    sylib
    wph
    @23
    @21
    vx
    cX
    wph
    vy
    vz
    vw
    cF
    cvv
    @10
    cY
    setrec1lem2.1
    @10
    cvv
    wcel
    wph
    vx
    vex
    a1i
    setrec1lem1
    ralbidv
    mpbid
    @18
    vx
    vz
    cX
    ralcom4
    sylib
    @19
    @13
    vz
    @19
    @6
    @11
    vx
    cX
    @18
    vx
    cX
    nfra1
    @6
    vx
    nfv
    @19
    @10
    cX
    wcel
    #
    @6
    @11
    @19
    @25
    @18
    @6
    @11
    wi
    @18
    vx
    cX
    rsp
    @25
    @6
    @17
    @11
    @25
    @5
    @16
    vw
    @25
    @15
    @2
    @4
    @25
    @10
    @0
    wss
    @15
    @2
    @10
    cX
    elssuni
    @1
    @10
    @0
    sstr2
    syl5com
    imim1d
    alimdv
    imim1d
    sylcom
    com23
    ralrimd
    alimi
    syl
    @8
    @13
    vz
    @7
    @12
    @6
    vx
    cX
    @3
    unissb
    imbi2i
    albii
    sylibr
    wph
    vy
    vz
    vw
    cF
    cvv
    @0
    cY
    setrec1lem2.1
    wph
    cX
    cV
    wcel
    @0
    cvv
    wcel
    setrec1lem2.2
    cX
    cV
    uniexg
    syl
    setrec1lem1
    mpbird
end
