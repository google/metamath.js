include "c-bnj18.mm"
include "wcel.mm"
include "cv.mm"
include "cfv.mm"
include "w3a.mm"
include "wex.mm"
include "wi.mm"
include "nfv.mm"
include "wfn.mm"
include "csuc.mm"
include "c-bnj14.mm"
include "ciun.mm"
include "wceq.mm"
include "com.mm"
include "wral.mm"
include "nfcv.mm"
include "nfiu1.mm"
include "nfeq2.mm"
include "nfim.mm"
include "nfral.mm"
include "nfxfr.mm"
include "nf5ri.mm"
include "bnj1096.mm"
include "nf5i.mm"
include "nf3an.mm"
include "nfex.mm"
include "eleq1.mm"
include "3anbi3d.mm"
include "3exbidv.mm"
include "imbi12d.mm"
include "bnj917.mm"
include "vtoclg1f.mm"
include "pm2.43i.mm"

theorem bnj981
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let vy: setvar y
  let cA: class A
  let cB: class B
  let cD: class D
  let cR: class R
  let vf: setvar f
  let vi: setvar i
  let vn: setvar n
  let cX: class X
  let cZ: class Z
  assume bnj981.1: |- ( ph <-> ( f ` (/) ) = _pred ( X , A , R ) )
  assume bnj981.2: |- ( ps <-> A. i e. _om ( suc i e. n -> ( f ` suc i ) = U_ y e. ( f ` i ) _pred ( y , A , R ) ) )
  assume bnj981.3: |- D = ( _om \ { (/) } )
  assume bnj981.4: |- B = { f | E. n e. D ( f Fn n /\ ph /\ ps ) }
  assume bnj981.5: |- ( ch <-> ( n e. D /\ f Fn n /\ ph /\ ps ) )

  disjoint A f
  disjoint A i
  disjoint A n
  disjoint A y
  disjoint f i
  disjoint f n
  disjoint f y
  disjoint i n
  disjoint i y
  disjoint n y
  disjoint D i
  disjoint D y
  disjoint R f
  disjoint R i
  disjoint R n
  disjoint R y
  disjoint X f
  disjoint X i
  disjoint X n
  disjoint X y
  disjoint Z f
  disjoint Z i
  disjoint Z n
  disjoint Z y
  disjoint i ph
  disjoint ph y
  assert |- ( Z e. _trCl ( X , A , R ) -> E. f E. n E. i ( ch /\ i e. n /\ Z e. ( f ` i ) ) )

  proof
    cZ
    cA
    cR
    cX
    c-bnj18
    #
    wcel
    #
    wch
    vi
    cv
    #
    vn
    cv
    #
    wcel
    #
    cZ
    @2
    vf
    cv
    #
    cfv
    #
    wcel
    #
    w3a
    #
    vi
    wex
    #
    vn
    wex
    #
    vf
    wex
    #
    vy
    cv
    #
    @0
    wcel
    #
    wch
    @4
    @12
    @6
    wcel
    #
    w3a
    #
    vi
    wex
    vn
    wex
    vf
    wex
    #
    wi
    @1
    @11
    wi
    vy
    cZ
    @0
    @1
    @11
    vy
    @1
    vy
    nfv
    @10
    vy
    vf
    @9
    vy
    vn
    @8
    vy
    vi
    wch
    @4
    @7
    vy
    wch
    vy
    wps
    wch
    @3
    cD
    wcel
    @5
    @3
    wfn
    wph
    vy
    wps
    vy
    wps
    @2
    csuc
    #
    @3
    wcel
    #
    @17
    @5
    cfv
    #
    vy
    @6
    cA
    cR
    @12
    c-bnj14
    #
    ciun
    #
    wceq
    #
    wi
    #
    vi
    com
    wral
    vy
    bnj981.2
    @23
    vy
    vi
    com
    vy
    com
    nfcv
    @18
    @22
    vy
    @18
    vy
    nfv
    vy
    @19
    @21
    vy
    @6
    @20
    nfiu1
    nfeq2
    nfim
    nfral
    nfxfr
    nf5ri
    bnj981.5
    bnj1096
    nf5i
    @4
    vy
    nfv
    @7
    vy
    nfv
    nf3an
    nfex
    nfex
    nfex
    nfim
    @12
    cZ
    wceq
    #
    @13
    @1
    @16
    @11
    @12
    cZ
    @0
    eleq1
    @24
    @15
    @8
    vf
    vn
    vi
    @24
    @14
    @7
    wch
    @4
    @12
    cZ
    @6
    eleq1
    3anbi3d
    3exbidv
    imbi12d
    wph
    wps
    wch
    vy
    cA
    cB
    cD
    cR
    vf
    vi
    vn
    cX
    bnj981.1
    bnj981.2
    bnj981.3
    bnj981.4
    bnj981.5
    bnj917
    vtoclg1f
    pm2.43i
end
