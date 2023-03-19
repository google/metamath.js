include "wcel.mm"
include "cop.mm"
include "co.mm"
include "wsbc.mm"
include "crab.mm"
include "wceq.mm"
include "wi.mm"
include "wa.mm"
include "mpt2xopoveq.mm"
include "ex.mm"
include "syl11.mm"
include "wn.mm"
include "c0.mm"
include "wnel.mm"
include "df-nel.mm"
include "cv.mm"
include "c1st.mm"
include "cfv.mm"
include "mpt2xopynvov0.mm"
include "sylbir.mm"
include "adantr.mm"
include "eqcomd.mm"
include "ancoms.mm"
include "eqtrd.mm"
include "pm2.61i.mm"

theorem mpt2xopoveqd
  let wph: wff ph
  let wps: wff ps
  let vx: setvar x
  let vy: setvar y
  let vn: setvar n
  let cF: class F
  let cK: class K
  let cV: class V
  let cW: class W
  let cX: class X
  let cY: class Y
  let cN: class N
  assume mpt2xopoveq.f: |- F = ( x e. _V , y e. ( 1st ` x ) |-> { n e. ( 1st ` x ) | ph } )
  assume mpt2xopoveqd.1: |- ( ps -> ( V e. X /\ W e. Y ) )
  assume mpt2xopoveqd.2: |- ( ( ps /\ -. K e. V ) -> { n e. V | [. <. V , W >. / x ]. [. K / y ]. ph } = (/) )

  disjoint K n
  disjoint K x
  disjoint K y
  disjoint n x
  disjoint n y
  disjoint x y
  disjoint V n
  disjoint V x
  disjoint V y
  disjoint W n
  disjoint W x
  disjoint W y
  disjoint X n
  disjoint X x
  disjoint X y
  disjoint Y n
  disjoint Y x
  disjoint Y y
  disjoint F x
  disjoint N x
  disjoint N y
  assert |- ( ps -> ( <. V , W >. F K ) = { n e. V | [. <. V , W >. / x ]. [. K / y ]. ph } )

  proof
    cK
    cV
    wcel
    #
    wps
    cV
    cW
    cop
    #
    cK
    cF
    co
    #
    wph
    vy
    cK
    wsbc
    vx
    @1
    wsbc
    vn
    cV
    crab
    #
    wceq
    #
    wi
    cV
    cX
    wcel
    cW
    cY
    wcel
    wa
    #
    @0
    @4
    wps
    @5
    @0
    @4
    wph
    vx
    vy
    vn
    cF
    cK
    cV
    cW
    cX
    cY
    mpt2xopoveq.f
    mpt2xopoveq
    ex
    mpt2xopoveqd.1
    syl11
    @0
    wn
    #
    wps
    @4
    @6
    wps
    wa
    @2
    c0
    @3
    @6
    @2
    c0
    wceq
    #
    wps
    @6
    cK
    cV
    wnel
    @7
    cK
    cV
    df-nel
    vx
    vy
    wph
    vn
    vx
    cv
    c1st
    cfv
    crab
    cF
    cK
    cV
    cW
    mpt2xopoveq.f
    mpt2xopynvov0
    sylbir
    adantr
    wps
    @6
    c0
    @3
    wceq
    wps
    @6
    wa
    @3
    c0
    mpt2xopoveqd.2
    eqcomd
    ancoms
    eqtrd
    ex
    pm2.61i
end
