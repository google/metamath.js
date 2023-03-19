include "cv.mm"
include "cfv.mm"
include "cop.mm"
include "cmpt2.mm"
include "ccnv.mm"
include "com.mm"
include "ccnf.mm"
include "co.mm"
include "c0.mm"
include "cfsupp.mm"
include "wbr.mm"
include "c2o.mm"
include "coe.mm"
include "cmap.mm"
include "crab.mm"
include "cid.mm"
include "cres.mm"
include "ccom.mm"
include "cmpt.mm"
include "comu.mm"
include "coa.mm"
include "eqid.mm"
include "infxpenc2lem2.mm"

theorem infxpenc2lem3
  let wph: wff ph
  let vx: setvar x
  let vw: setvar w
  let cA: class A
  let vg: setvar g
  let vn: setvar n
  let cF: class F
  let cW: class W
  let vb: setvar b
  let vy: setvar y
  let vz: setvar z
  let cG: class G
  let cX: class X
  let cY: class Y
  assume infxpenc2.1: |- ( ph -> A e. On )
  assume infxpenc2.2: |- ( ph -> A. b e. A ( _om C_ b -> E. w e. ( On \ 1o ) ( n ` b ) : b -1-1-onto-> ( _om ^o w ) ) )
  assume infxpenc2.3: |- W = ( `' ( x e. ( On \ 1o ) |-> ( _om ^o x ) ) ` ran ( n ` b ) )
  assume infxpenc2.4: |- ( ph -> F : ( _om ^o 2o ) -1-1-onto-> _om )
  assume infxpenc2.5: |- ( ph -> ( F ` (/) ) = (/) )

  disjoint b g
  disjoint b n
  disjoint b w
  disjoint b x
  disjoint A b
  disjoint g n
  disjoint g w
  disjoint g x
  disjoint A g
  disjoint n w
  disjoint n x
  disjoint A n
  disjoint w x
  disjoint A w
  disjoint A x
  disjoint b ph
  disjoint ph w
  disjoint ph x
  disjoint W g
  disjoint W w
  disjoint W x
  disjoint F g
  disjoint F x
  disjoint b y
  disjoint g y
  disjoint n y
  disjoint w y
  disjoint x y
  disjoint A y
  disjoint ph y
  disjoint g z
  disjoint w z
  disjoint x z
  disjoint y z
  disjoint W y
  disjoint W z
  disjoint F y
  disjoint G g
  disjoint X x
  disjoint X y
  disjoint Y x
  disjoint Y y
  assert |- ( ph -> E. g A. b e. A ( _om C_ b -> ( g ` b ) : ( b X. b ) -1-1-onto-> b ) )

  proof
    wph
    vx
    vy
    vz
    vw
    cA
    vx
    vy
    vb
    cv
    #
    @0
    vx
    cv
    #
    @0
    vn
    cv
    cfv
    #
    cfv
    vy
    cv
    #
    @2
    cfv
    cop
    cmpt2
    #
    vg
    vn
    cF
    @2
    ccnv
    com
    cW
    ccnf
    co
    vy
    @1
    c0
    cfsupp
    wbr
    #
    vx
    com
    c2o
    coe
    co
    #
    cW
    cmap
    co
    crab
    cF
    @3
    cid
    cW
    cres
    ccnv
    ccom
    ccom
    cmpt
    #
    ccom
    @6
    cW
    ccnf
    co
    ccnv
    ccom
    #
    com
    c2o
    cW
    comu
    co
    ccnf
    co
    vy
    @5
    vx
    com
    cW
    c2o
    comu
    co
    #
    cmap
    co
    crab
    cid
    com
    cres
    @3
    vz
    vw
    c2o
    cW
    c2o
    vw
    cv
    #
    comu
    co
    vz
    cv
    #
    coa
    co
    cmpt2
    #
    vz
    vw
    c2o
    cW
    cW
    @11
    comu
    co
    @10
    coa
    co
    cmpt2
    #
    ccnv
    ccom
    ccnv
    ccom
    ccom
    cmpt
    #
    ccom
    com
    @9
    ccnf
    co
    ccnv
    ccom
    #
    ccom
    vx
    vy
    com
    cW
    coe
    co
    #
    @16
    @16
    @1
    comu
    co
    @3
    coa
    co
    cmpt2
    #
    ccom
    @4
    ccom
    ccom
    #
    @8
    @15
    @7
    @14
    cW
    @13
    @12
    @17
    vb
    infxpenc2.1
    infxpenc2.2
    infxpenc2.3
    infxpenc2.4
    infxpenc2.5
    @7
    eqid
    @8
    eqid
    @14
    eqid
    @13
    eqid
    @12
    eqid
    @15
    eqid
    @17
    eqid
    @4
    eqid
    @18
    eqid
    infxpenc2lem2
end
