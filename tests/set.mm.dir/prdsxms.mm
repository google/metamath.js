include "wcel.mm"
include "cfn.mm"
include "cxme.mm"
include "wf.mm"
include "w3a.mm"
include "cds.mm"
include "cfv.mm"
include "cbs.mm"
include "cxp.mm"
include "cres.mm"
include "cxmt.mm"
include "ctopn.mm"
include "cmopn.mm"
include "wceq.mm"
include "wss.mm"
include "simp1.mm"
include "simp2.mm"
include "eqid.mm"
include "simp3.mm"
include "prdsxmslem1.mm"
include "ssid.mm"
include "xmetres2.mm"
include "sylancl.mm"
include "cv.mm"
include "wfn.mm"
include "ccom.mm"
include "wral.mm"
include "cuni.mm"
include "cdif.mm"
include "wrex.mm"
include "cixp.mm"
include "wa.mm"
include "wex.mm"
include "cab.mm"
include "prdsxmslem2.mm"
include "cxr.mm"
include "xmetf.mm"
include "ffn.mm"
include "fnresdm.mm"
include "4syl.mm"
include "fveq2d.mm"
include "eqtr4d.mm"
include "isxms2.mm"
include "sylanbrc.mm"

theorem prdsxms
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


  assert |- ( ( S e. W /\ I e. Fin /\ R : I --> *MetSp ) -> Y e. *MetSp )

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
    cxme
    cR
    wf
    #
    w3a
    #
    cY
    cds
    cfv
    #
    cY
    cbs
    cfv
    #
    @5
    cxp
    #
    cres
    #
    @5
    cxmt
    cfv
    #
    wcel
    #
    cY
    ctopn
    cfv
    #
    @7
    cmopn
    cfv
    #
    wceq
    cY
    cxme
    wcel
    @3
    @4
    @8
    wcel
    #
    @5
    @5
    wss
    @9
    @3
    @5
    @4
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
    #
    @0
    @1
    @2
    simp2
    #
    @4
    eqid
    #
    @5
    eqid
    #
    @0
    @1
    @2
    simp3
    #
    prdsxmslem1
    #
    @5
    ssid
    @4
    @5
    @5
    xmetres2
    sylancl
    @3
    @10
    @4
    cmopn
    cfv
    @11
    @3
    vx
    vz
    @5
    vg
    cv
    #
    cI
    wfn
    vk
    cv
    #
    @19
    cfv
    #
    @20
    ctopn
    cR
    ccom
    cfv
    #
    wcel
    vk
    cI
    wral
    @21
    @22
    cuni
    wceq
    vk
    cI
    vz
    cv
    cdif
    wral
    vz
    cfn
    wrex
    w3a
    vx
    cv
    vk
    cI
    @21
    cixp
    wceq
    wa
    vg
    wex
    vx
    cab
    #
    @4
    cR
    cS
    vg
    vk
    @20
    cR
    cfv
    #
    cds
    cfv
    @24
    cbs
    cfv
    #
    @25
    cxp
    cres
    #
    cI
    @10
    @24
    ctopn
    cfv
    #
    @25
    cW
    cY
    prdsxms.y
    @13
    @14
    @15
    @16
    @17
    @10
    eqid
    #
    @25
    eqid
    @26
    eqid
    @27
    eqid
    @23
    eqid
    prdsxmslem2
    @3
    @7
    @4
    cmopn
    @3
    @12
    @6
    cxr
    @4
    wf
    @4
    @6
    wfn
    @7
    @4
    wceq
    @18
    @4
    @5
    xmetf
    @6
    cxr
    @4
    ffn
    @6
    @4
    fnresdm
    4syl
    fveq2d
    eqtr4d
    @7
    @10
    cY
    @5
    @28
    @16
    @7
    eqid
    isxms2
    sylanbrc
end
