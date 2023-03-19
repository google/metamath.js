include "ccnrm.mm"
include "wcel.mm"
include "cuni.mm"
include "crest.mm"
include "co.mm"
include "cnrm.mm"
include "eqid.mm"
include "restid.mm"
include "cvv.mm"
include "uniexg.mm"
include "cnrmi.mm"
include "mpdan.mm"
include "eqeltrrd.mm"

theorem cnrmnrm
  let cJ: class J
  let vf: setvar f
  let vg: setvar g
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let cA: class A
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
  let cV: class V
  let cX: class X
  let cY: class Y


  assert |- ( J e. CNrm -> J e. Nrm )

  proof
    cJ
    ccnrm
    wcel
    #
    cJ
    cJ
    cuni
    #
    crest
    co
    #
    cJ
    cnrm
    cJ
    ccnrm
    @1
    @1
    eqid
    restid
    @0
    @1
    cvv
    wcel
    @2
    cnrm
    wcel
    cJ
    ccnrm
    uniexg
    @1
    cJ
    cvv
    cnrmi
    mpdan
    eqeltrrd
end
