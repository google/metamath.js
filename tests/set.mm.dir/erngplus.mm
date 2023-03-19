include "chlt.mm"
include "wcel.mm"
include "wa.mm"
include "co.mm"
include "cv.mm"
include "cfv.mm"
include "ccom.mm"
include "cmpt.mm"
include "cmpt2.mm"
include "erngfplus.mm"
include "oveqd.mm"
include "eqid.mm"
include "tendopl.mm"
include "sylan9eq.mm"

theorem erngplus
  let cD: class D
  let c.pl: class .+
  let cT: class T
  let cU: class U
  let vf: setvar f
  let cE: class E
  let cH: class H
  let cK: class K
  let cV: class V
  let cW: class W
  let vg: setvar g
  let vs: setvar s
  let vt: setvar t
  let vk: setvar k
  let vw: setvar w
  assume erngset.h: |- H = ( LHyp ` K )
  assume erngset.t: |- T = ( ( LTrn ` K ) ` W )
  assume erngset.e: |- E = ( ( TEndo ` K ) ` W )
  assume erngset.d: |- D = ( ( EDRing ` K ) ` W )
  assume erng.p: |- .+ = ( +g ` D )

  disjoint T f
  disjoint U f
  disjoint V f
  disjoint K f
  disjoint W f
  disjoint K g
  disjoint f g
  disjoint f s
  disjoint f t
  disjoint g s
  disjoint g t
  disjoint T g
  disjoint s t
  disjoint T s
  disjoint T t
  disjoint U g
  disjoint U s
  disjoint U t
  disjoint V g
  disjoint V s
  disjoint V t
  disjoint W g
  disjoint E k
  disjoint k w
  disjoint H k
  disjoint H w
  disjoint f k
  disjoint f s
  disjoint f t
  disjoint f w
  disjoint k s
  disjoint k t
  disjoint K k
  disjoint s t
  disjoint s w
  disjoint K s
  disjoint t w
  disjoint K t
  disjoint K w
  disjoint T k
  disjoint E w
  disjoint T w
  disjoint W s
  disjoint W t
  disjoint W w
  disjoint E s
  disjoint E t
  assert |- ( ( ( K e. HL /\ W e. H ) /\ ( U e. E /\ V e. E ) ) -> ( U .+ V ) = ( f e. T |-> ( ( U ` f ) o. ( V ` f ) ) ) )

  proof
    cK
    chlt
    wcel
    cW
    cH
    wcel
    wa
    #
    cU
    cE
    wcel
    cV
    cE
    wcel
    wa
    cU
    cV
    c.pl
    co
    cU
    cV
    vs
    vt
    cE
    cE
    vg
    cT
    vg
    cv
    #
    vs
    cv
    cfv
    @1
    vt
    cv
    cfv
    ccom
    cmpt
    cmpt2
    #
    co
    vf
    cT
    vf
    cv
    #
    cU
    cfv
    @3
    cV
    cfv
    ccom
    cmpt
    @0
    c.pl
    @2
    cU
    cV
    vt
    cD
    c.pl
    cT
    vg
    cE
    cH
    cK
    chlt
    cW
    vs
    erngset.h
    erngset.t
    erngset.e
    erngset.d
    erng.p
    erngfplus
    oveqd
    vt
    @2
    cT
    cU
    vg
    vf
    cE
    cK
    cV
    cW
    vs
    @2
    eqid
    erngset.t
    tendopl
    sylan9eq
end
