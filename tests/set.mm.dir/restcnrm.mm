include "ccnrm.mm"
include "wcel.mm"
include "wa.mm"
include "crest.mm"
include "co.mm"
include "cuni.mm"
include "cin.mm"
include "eqid.mm"
include "restin.mm"
include "cv.mm"
include "cnrm.mm"
include "cpw.mm"
include "wral.mm"
include "wss.mm"
include "cvv.mm"
include "wceq.mm"
include "simpll.mm"
include "elpwi.mm"
include "adantl.mm"
include "inex1g.mm"
include "ad2antlr.mm"
include "restabs.mm"
include "syl3anc.mm"
include "cnrmi.mm"
include "adantlr.mm"
include "eqeltrd.mm"
include "ralrimiva.mm"
include "ctopon.mm"
include "cfv.mm"
include "wb.mm"
include "ctop.mm"
include "cnrmtop.mm"
include "adantr.mm"
include "toptopon.mm"
include "sylib.mm"
include "inss2.mm"
include "resttopon.mm"
include "sylancl.mm"
include "iscnrm2.mm"
include "syl.mm"
include "mpbird.mm"

theorem restcnrm
  let cA: class A
  let cJ: class J
  let cV: class V
  let vf: setvar f
  let vg: setvar g
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let cB: class B
  let cC: class C
  let cD: class D
  let vu: setvar u
  let vv: setvar v
  let vw: setvar w
  let cK: class K
  let vm: setvar m
  let vn: setvar n
  let cF: class F
  let vc: setvar c
  let vd: setvar d
  let vj: setvar j
  let vo: setvar o
  let cU: class U
  let cX: class X
  let cY: class Y


  assert |- ( ( J e. CNrm /\ A e. V ) -> ( J |`t A ) e. CNrm )

  proof
    cJ
    ccnrm
    wcel
    #
    cA
    cV
    wcel
    #
    wa
    #
    cJ
    cA
    crest
    co
    cJ
    cA
    cJ
    cuni
    #
    cin
    #
    crest
    co
    #
    ccnrm
    cA
    cJ
    ccnrm
    cV
    @3
    @3
    eqid
    #
    restin
    @2
    @5
    ccnrm
    wcel
    #
    @5
    vx
    cv
    #
    crest
    co
    #
    cnrm
    wcel
    #
    vx
    @4
    cpw
    #
    wral
    #
    @2
    @10
    vx
    @11
    @2
    @8
    @11
    wcel
    #
    wa
    #
    @9
    cJ
    @8
    crest
    co
    #
    cnrm
    @14
    @0
    @8
    @4
    wss
    #
    @4
    cvv
    wcel
    #
    @9
    @15
    wceq
    @0
    @1
    @13
    simpll
    @13
    @16
    @2
    @8
    @4
    elpwi
    adantl
    @1
    @17
    @0
    @13
    cA
    @3
    cV
    inex1g
    ad2antlr
    @8
    @4
    cJ
    ccnrm
    cvv
    restabs
    syl3anc
    @0
    @13
    @15
    cnrm
    wcel
    @1
    @8
    cJ
    @11
    cnrmi
    adantlr
    eqeltrd
    ralrimiva
    @2
    @5
    @4
    ctopon
    cfv
    wcel
    #
    @7
    @12
    wb
    @2
    cJ
    @3
    ctopon
    cfv
    wcel
    #
    @4
    @3
    wss
    @18
    @2
    cJ
    ctop
    wcel
    #
    @19
    @0
    @20
    @1
    cJ
    cnrmtop
    adantr
    cJ
    @3
    @6
    toptopon
    sylib
    cA
    @3
    inss2
    @4
    cJ
    @3
    resttopon
    sylancl
    vx
    @5
    @4
    iscnrm2
    syl
    mpbird
    eqeltrd
end
