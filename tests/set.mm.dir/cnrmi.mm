include "ccnrm.mm"
include "wcel.mm"
include "wa.mm"
include "crest.mm"
include "co.mm"
include "cuni.mm"
include "cin.mm"
include "cnrm.mm"
include "eqid.mm"
include "restin.mm"
include "cpw.mm"
include "cv.mm"
include "wral.mm"
include "wss.mm"
include "inss2.mm"
include "cvv.mm"
include "wb.mm"
include "inex1g.mm"
include "elpwg.mm"
include "syl.mm"
include "mpbiri.mm"
include "adantl.mm"
include "ctop.mm"
include "iscnrm.mm"
include "simprbi.mm"
include "adantr.mm"
include "wceq.mm"
include "oveq2.mm"
include "eleq1d.mm"
include "rspcv.mm"
include "sylc.mm"
include "eqeltrd.mm"

theorem cnrmi
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


  assert |- ( ( J e. CNrm /\ A e. V ) -> ( J |`t A ) e. Nrm )

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
    cnrm
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
    @4
    @3
    cpw
    #
    wcel
    #
    cJ
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
    @7
    wral
    #
    @5
    cnrm
    wcel
    #
    @1
    @8
    @0
    @1
    @8
    @4
    @3
    wss
    #
    cA
    @3
    inss2
    @1
    @4
    cvv
    wcel
    @8
    @14
    wb
    cA
    @3
    cV
    inex1g
    @4
    @3
    cvv
    elpwg
    syl
    mpbiri
    adantl
    @0
    @12
    @1
    @0
    cJ
    ctop
    wcel
    @12
    vx
    cJ
    @3
    @6
    iscnrm
    simprbi
    adantr
    @11
    @13
    vx
    @4
    @7
    @9
    @4
    wceq
    @10
    @5
    cnrm
    @9
    @4
    cJ
    crest
    oveq2
    eleq1d
    rspcv
    sylc
    eqeltrd
end
