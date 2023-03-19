include "cn.mm"
include "csquarenn.mm"
include "cdif.mm"
include "wcel.mm"
include "cpell14qr.mm"
include "cfv.mm"
include "cz.mm"
include "cexp.mm"
include "co.mm"
include "cr.mm"
include "cn0.mm"
include "cneg.mm"
include "wo.mm"
include "wa.mm"
include "elznn0.mm"
include "simplll.mm"
include "simpllr.mm"
include "simpr.mm"
include "pell14qrexpclnn0.mm"
include "syl3anc.mm"
include "c1.mm"
include "cdiv.mm"
include "cc.mm"
include "wceq.mm"
include "pell14qrre.mm"
include "recnd.mm"
include "ad2antrr.mm"
include "simplr.mm"
include "expneg2.mm"
include "pell14qrreccl.mm"
include "syl2anc.mm"
include "eqeltrd.mm"
include "jaodan.mm"
include "expl.mm"
include "syl5bi.mm"
include "3impia.mm"

theorem pell14qrexpcl
  let cA: class A
  let cB: class B
  let cD: class D
  let va: setvar a
  let vb: setvar b
  let vc: setvar c
  let vd: setvar d
  let ve: setvar e
  let vf: setvar f
  let vw: setvar w
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z


  assert |- ( ( D e. ( NN \ []NN ) /\ A e. ( Pell14QR ` D ) /\ B e. ZZ ) -> ( A ^ B ) e. ( Pell14QR ` D ) )

  proof
    cD
    cn
    csquarenn
    cdif
    wcel
    #
    cA
    cD
    cpell14qr
    cfv
    #
    wcel
    #
    cB
    cz
    wcel
    #
    cA
    cB
    cexp
    co
    #
    @1
    wcel
    #
    @3
    cB
    cr
    wcel
    #
    cB
    cn0
    wcel
    #
    cB
    cneg
    #
    cn0
    wcel
    #
    wo
    #
    wa
    @0
    @2
    wa
    #
    @5
    cB
    elznn0
    @11
    @6
    @10
    @5
    @11
    @6
    wa
    #
    @7
    @5
    @9
    @12
    @7
    wa
    @0
    @2
    @7
    @5
    @0
    @2
    @6
    @7
    simplll
    @0
    @2
    @6
    @7
    simpllr
    @12
    @7
    simpr
    cA
    cB
    cD
    pell14qrexpclnn0
    syl3anc
    @12
    @9
    wa
    #
    @4
    c1
    cA
    @8
    cexp
    co
    #
    cdiv
    co
    #
    @1
    @13
    cA
    cc
    wcel
    #
    cB
    cc
    wcel
    @9
    @4
    @15
    wceq
    @11
    @16
    @6
    @9
    @11
    cA
    cA
    cD
    pell14qrre
    recnd
    ad2antrr
    @13
    cB
    @11
    @6
    @9
    simplr
    recnd
    @12
    @9
    simpr
    #
    cA
    cB
    expneg2
    syl3anc
    @13
    @0
    @14
    @1
    wcel
    #
    @15
    @1
    wcel
    @0
    @2
    @6
    @9
    simplll
    #
    @13
    @0
    @2
    @9
    @18
    @19
    @0
    @2
    @6
    @9
    simpllr
    @17
    cA
    @8
    cD
    pell14qrexpclnn0
    syl3anc
    @14
    cD
    pell14qrreccl
    syl2anc
    eqeltrd
    jaodan
    expl
    syl5bi
    3impia
end
