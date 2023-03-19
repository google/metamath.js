include "wcel.mm"
include "cfn.mm"
include "cmt.mm"
include "wf.mm"
include "w3a.mm"
include "cxme.mm"
include "cds.mm"
include "cfv.mm"
include "cbs.mm"
include "cxp.mm"
include "cres.mm"
include "cme.mm"
include "wss.mm"
include "cv.mm"
include "msxms.mm"
include "ssriv.mm"
include "fss.mm"
include "mpan2.mm"
include "prdsxms.mm"
include "syl3an3.mm"
include "simp1.mm"
include "simp2.mm"
include "eqid.mm"
include "simp3.mm"
include "prdsmslem1.mm"
include "ssid.mm"
include "metres2.mm"
include "sylancl.mm"
include "ctopn.mm"
include "isms.mm"
include "sylanbrc.mm"

theorem prdsms
  let cR: class R
  let cS: class S
  let cI: class I
  let cW: class W
  let cY: class Y
  let vg: setvar g
  let vk: setvar k
  let vp: setvar p
  let vr: setvar r
  let vw: setvar w
  let vy: setvar y
  let cB: class B
  let vm: setvar m
  let vu: setvar u
  let vx: setvar x
  let cD: class D
  let vn: setvar n
  let vz: setvar z
  let cC: class C
  let cE: class E
  let cK: class K
  let wph: wff ph
  let cV: class V
  assume prdsxms.y: |- Y = ( S Xs_ R )


  assert |- ( ( S e. W /\ I e. Fin /\ R : I --> MetSp ) -> Y e. MetSp )

  proof
    cS
    cW
    wcel
    #
    cI
    cfn
    wcel
    #
    cI
    cmt
    cR
    wf
    #
    w3a
    #
    cY
    cxme
    wcel
    #
    cY
    cds
    cfv
    #
    cY
    cbs
    cfv
    #
    @6
    cxp
    cres
    #
    @6
    cme
    cfv
    #
    wcel
    #
    cY
    cmt
    wcel
    @2
    @0
    @1
    cI
    cxme
    cR
    wf
    #
    @4
    @2
    cmt
    cxme
    wss
    @10
    vx
    cmt
    cxme
    vx
    cv
    msxms
    ssriv
    cI
    cmt
    cxme
    cR
    fss
    mpan2
    cR
    cS
    cI
    cW
    cY
    prdsxms.y
    prdsxms
    syl3an3
    @3
    @5
    @8
    wcel
    @6
    @6
    wss
    @9
    @3
    @6
    @5
    cR
    cS
    cI
    cW
    cY
    prdsxms.y
    @0
    @1
    @2
    simp1
    @0
    @1
    @2
    simp2
    @5
    eqid
    @6
    eqid
    #
    @0
    @1
    @2
    simp3
    prdsmslem1
    @6
    ssid
    @5
    @6
    @6
    metres2
    sylancl
    @7
    cY
    ctopn
    cfv
    #
    cY
    @6
    @12
    eqid
    @11
    @7
    eqid
    isms
    sylanbrc
end
