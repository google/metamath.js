include "cfv.mm"
include "cun.mm"
include "wcel.mm"
include "cv.mm"
include "wss.mm"
include "wi.mm"
include "wal.mm"
include "wa.mm"
include "id.mm"
include "ssun1.mm"
include "syl6ss.mm"
include "imim1i.mm"
include "alimi.mm"
include "setrec1lem1.mm"
include "mpbid.mm"
include "sp.mm"
include "syl.mm"
include "sstr2.mm"
include "syld.mm"
include "cvv.mm"
include "wceq.mm"
include "sseq1.mm"
include "fveq2.mm"
include "sseq1d.mm"
include "imbi12d.mm"
include "spcdvw.mm"
include "mpid.mm"
include "mpdd.mm"
include "jcad.mm"
include "syl5.mm"
include "unss.mm"
include "syl6ib.mm"
include "alrimi.mm"
include "fvex.mm"
include "unexg.mm"
include "sylancl.mm"
include "mpbird.mm"

theorem setrec1lem4
  let wph: wff ph
  let vy: setvar y
  let vz: setvar z
  let vw: setvar w
  let cA: class A
  let cF: class F
  let cX: class X
  let cY: class Y
  let vk: setvar k
  let vx: setvar x
  assume setrec1lem4.1: |- F/ z ph
  assume setrec1lem4.2: |- Y = { y | A. z ( A. w ( w C_ y -> ( w C_ z -> ( F ` w ) C_ z ) ) -> y C_ z ) }
  assume setrec1lem4.3: |- ( ph -> A e. _V )
  assume setrec1lem4.4: |- ( ph -> A C_ X )
  assume setrec1lem4.5: |- ( ph -> X e. Y )

  disjoint w y
  disjoint w z
  disjoint A w
  disjoint y z
  disjoint A y
  disjoint A z
  disjoint F w
  disjoint F y
  disjoint F z
  disjoint X w
  disjoint X y
  disjoint X z
  disjoint k x
  assert |- ( ph -> ( X u. ( F ` A ) ) e. Y )

  proof
    wph
    cX
    cA
    cF
    cfv
    #
    cun
    #
    cY
    wcel
    vw
    cv
    #
    @1
    wss
    #
    @2
    vz
    cv
    #
    wss
    #
    @2
    cF
    cfv
    #
    @4
    wss
    #
    wi
    #
    wi
    #
    vw
    wal
    #
    @1
    @4
    wss
    #
    wi
    #
    vz
    wal
    wph
    @12
    vz
    setrec1lem4.1
    wph
    @10
    cX
    @4
    wss
    #
    @0
    @4
    wss
    #
    wa
    #
    @11
    @10
    @2
    cX
    wss
    #
    @8
    wi
    #
    vw
    wal
    #
    wph
    @15
    @9
    @17
    vw
    @16
    @3
    @8
    @16
    @2
    cX
    @1
    @16
    id
    cX
    @0
    ssun1
    syl6ss
    imim1i
    alimi
    wph
    @18
    @13
    @14
    wph
    @18
    @13
    wi
    #
    vz
    wal
    #
    @19
    wph
    cX
    cY
    wcel
    #
    @20
    setrec1lem4.5
    wph
    vy
    vz
    vw
    cF
    cY
    cX
    cY
    setrec1lem4.2
    setrec1lem4.5
    setrec1lem1
    mpbid
    @19
    vz
    sp
    syl
    #
    wph
    @18
    cA
    @4
    wss
    #
    @14
    wph
    @18
    @13
    @23
    @22
    wph
    cA
    cX
    wss
    #
    @13
    @23
    wi
    setrec1lem4.4
    cA
    cX
    @4
    sstr2
    syl
    syld
    wph
    @18
    @24
    @23
    @14
    wi
    #
    setrec1lem4.4
    wph
    @17
    @24
    @25
    wi
    vw
    cA
    cvv
    setrec1lem4.3
    @2
    cA
    wceq
    #
    @16
    @24
    @8
    @25
    @2
    cA
    cX
    sseq1
    @26
    @5
    @23
    @7
    @14
    @2
    cA
    @4
    sseq1
    @26
    @6
    @0
    @4
    @2
    cA
    cF
    fveq2
    sseq1d
    imbi12d
    imbi12d
    spcdvw
    mpid
    mpdd
    jcad
    syl5
    cX
    @0
    @4
    unss
    syl6ib
    alrimi
    wph
    vy
    vz
    vw
    cF
    cvv
    @1
    cY
    setrec1lem4.2
    wph
    @21
    @0
    cvv
    wcel
    @1
    cvv
    wcel
    setrec1lem4.5
    cA
    cF
    fvex
    cX
    @0
    cY
    cvv
    unexg
    sylancl
    setrec1lem1
    mpbird
end
