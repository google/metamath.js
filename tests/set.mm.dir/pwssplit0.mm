include "wcel.mm"
include "wss.mm"
include "w3a.mm"
include "cv.mm"
include "cres.mm"
include "wa.mm"
include "cbs.mm"
include "cfv.mm"
include "wf.mm"
include "wb.mm"
include "eqid.mm"
include "pwselbasb.mm"
include "3adant3.mm"
include "biimpa.mm"
include "simpl3.mm"
include "fssresd.mm"
include "cvv.mm"
include "simp1.mm"
include "simp2.mm"
include "simp3.mm"
include "ssexd.mm"
include "syl2anc.mm"
include "adantr.mm"
include "mpbird.mm"
include "fmptd.mm"

theorem pwssplit0
  let vx: setvar x
  let cB: class B
  let cC: class C
  let cT: class T
  let cU: class U
  let cF: class F
  let cV: class V
  let cW: class W
  let cX: class X
  let cY: class Y
  let cZ: class Z
  let va: setvar a
  let vb: setvar b
  assume pwssplit1.y: |- Y = ( W ^s U )
  assume pwssplit1.z: |- Z = ( W ^s V )
  assume pwssplit1.b: |- B = ( Base ` Y )
  assume pwssplit1.c: |- C = ( Base ` Z )
  assume pwssplit1.f: |- F = ( x e. B |-> ( x |` V ) )

  disjoint Y x
  disjoint W x
  disjoint U x
  disjoint Z x
  disjoint V x
  disjoint B x
  disjoint C x
  disjoint X x
  disjoint T x
  disjoint Y a
  disjoint Y b
  disjoint a b
  disjoint a x
  disjoint b x
  disjoint W a
  disjoint W b
  disjoint U a
  disjoint U b
  disjoint Z a
  disjoint Z b
  disjoint V a
  disjoint V b
  disjoint B a
  disjoint B b
  disjoint C a
  disjoint C b
  disjoint F a
  disjoint F b
  disjoint X a
  disjoint X b
  assert |- ( ( W e. T /\ U e. X /\ V C_ U ) -> F : B --> C )

  proof
    cW
    cT
    wcel
    #
    cU
    cX
    wcel
    #
    cV
    cU
    wss
    #
    w3a
    #
    vx
    cB
    vx
    cv
    #
    cV
    cres
    #
    cC
    cF
    @3
    @4
    cB
    wcel
    #
    wa
    #
    @5
    cC
    wcel
    #
    cV
    cW
    cbs
    cfv
    #
    @5
    wf
    #
    @7
    cU
    @9
    cV
    @4
    @3
    @6
    cU
    @9
    @4
    wf
    #
    @0
    @1
    @6
    @11
    wb
    @2
    @9
    cW
    cU
    cB
    cT
    @4
    cY
    cX
    pwssplit1.y
    @9
    eqid
    #
    pwssplit1.b
    pwselbasb
    3adant3
    biimpa
    @0
    @1
    @2
    @6
    simpl3
    fssresd
    @3
    @8
    @10
    wb
    #
    @6
    @3
    @0
    cV
    cvv
    wcel
    @13
    @0
    @1
    @2
    simp1
    @3
    cV
    cU
    cX
    @0
    @1
    @2
    simp2
    @0
    @1
    @2
    simp3
    ssexd
    @9
    cW
    cV
    cC
    cT
    @5
    cZ
    cvv
    pwssplit1.z
    @12
    pwssplit1.c
    pwselbasb
    syl2anc
    adantr
    mpbird
    pwssplit1.f
    fmptd
end
