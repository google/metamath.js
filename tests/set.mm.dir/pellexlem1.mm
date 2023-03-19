include "cn.mm"
include "wcel.mm"
include "w3a.mm"
include "csqrt.mm"
include "cfv.mm"
include "cq.mm"
include "wn.mm"
include "c2.mm"
include "cexp.mm"
include "co.mm"
include "cmul.mm"
include "cmin.mm"
include "cc0.mm"
include "wne.mm"
include "wceq.mm"
include "cc.mm"
include "nncn.mm"
include "3ad2ant2.mm"
include "sqcld.mm"
include "3ad2ant1.mm"
include "3ad2ant3.mm"
include "mulcld.mm"
include "subeq0ad.mm"
include "cdiv.mm"
include "nnne0.mm"
include "wb.mm"
include "sqne0.mm"
include "syl.mm"
include "mpbird.mm"
include "divmul3d.mm"
include "sqdiv.mm"
include "fveq2d.mm"
include "syl3anc.mm"
include "cr.mm"
include "nnre.mm"
include "redivcld.mm"
include "cle.mm"
include "wbr.mm"
include "clt.mm"
include "nnnn0.mm"
include "nn0ge0d.mm"
include "nngt0.mm"
include "divge0.mm"
include "syl22anc.mm"
include "sqrtsqd.mm"
include "eqtr3d.mm"
include "nnq.mm"
include "qdivcl.mm"
include "eqeltrd.mm"
include "fveq2.mm"
include "eleq1d.mm"
include "syl5ibcom.mm"
include "sylbird.mm"
include "sylbid.mm"
include "necon3bd.mm"
include "imp.mm"

theorem pellexlem1
  let cA: class A
  let cB: class B
  let cD: class D
  let va: setvar a
  let vb: setvar b
  let vc: setvar c
  let vd: setvar d
  let ve: setvar e
  let vf: setvar f
  let vg: setvar g
  let cC: class C
  let cE: class E
  let cF: class F
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let wph: wff ph


  assert |- ( ( ( D e. NN /\ A e. NN /\ B e. NN ) /\ -. ( sqrt ` D ) e. QQ ) -> ( ( A ^ 2 ) - ( D x. ( B ^ 2 ) ) ) =/= 0 )

  proof
    cD
    cn
    wcel
    #
    cA
    cn
    wcel
    #
    cB
    cn
    wcel
    #
    w3a
    #
    cD
    csqrt
    cfv
    #
    cq
    wcel
    #
    wn
    cA
    c2
    cexp
    co
    #
    cD
    cB
    c2
    cexp
    co
    #
    cmul
    co
    #
    cmin
    co
    #
    cc0
    wne
    @3
    @5
    @9
    cc0
    @3
    @9
    cc0
    wceq
    @6
    @8
    wceq
    #
    @5
    @3
    @6
    @8
    @3
    cA
    @1
    @0
    cA
    cc
    wcel
    #
    @2
    cA
    nncn
    3ad2ant2
    #
    sqcld
    #
    @3
    cD
    @7
    @0
    @1
    cD
    cc
    wcel
    @2
    cD
    nncn
    3ad2ant1
    #
    @3
    cB
    @2
    @0
    cB
    cc
    wcel
    #
    @1
    cB
    nncn
    3ad2ant3
    #
    sqcld
    #
    mulcld
    subeq0ad
    @3
    @10
    @6
    @7
    cdiv
    co
    #
    cD
    wceq
    #
    @5
    @3
    @6
    cD
    @7
    @13
    @14
    @17
    @3
    @7
    cc0
    wne
    #
    cB
    cc0
    wne
    #
    @2
    @0
    @21
    @1
    cB
    nnne0
    3ad2ant3
    #
    @3
    @15
    @20
    @21
    wb
    @16
    cB
    sqne0
    syl
    mpbird
    divmul3d
    @3
    @18
    csqrt
    cfv
    #
    cq
    wcel
    @19
    @5
    @3
    @23
    cA
    cB
    cdiv
    co
    #
    cq
    @3
    @24
    c2
    cexp
    co
    #
    csqrt
    cfv
    #
    @23
    @24
    @3
    @11
    @15
    @21
    @26
    @23
    wceq
    @12
    @16
    @22
    @11
    @15
    @21
    w3a
    @25
    @18
    csqrt
    cA
    cB
    sqdiv
    fveq2d
    syl3anc
    @3
    @24
    @3
    cA
    cB
    @1
    @0
    cA
    cr
    wcel
    #
    @2
    cA
    nnre
    3ad2ant2
    #
    @2
    @0
    cB
    cr
    wcel
    #
    @1
    cB
    nnre
    3ad2ant3
    #
    @22
    redivcld
    @3
    @27
    cc0
    cA
    cle
    wbr
    #
    @29
    cc0
    cB
    clt
    wbr
    #
    cc0
    @24
    cle
    wbr
    @28
    @1
    @0
    @31
    @2
    @1
    cA
    cA
    nnnn0
    nn0ge0d
    3ad2ant2
    @30
    @2
    @0
    @32
    @1
    cB
    nngt0
    3ad2ant3
    cA
    cB
    divge0
    syl22anc
    sqrtsqd
    eqtr3d
    @3
    cA
    cq
    wcel
    #
    cB
    cq
    wcel
    #
    @21
    @24
    cq
    wcel
    @1
    @0
    @33
    @2
    cA
    nnq
    3ad2ant2
    @2
    @0
    @34
    @1
    cB
    nnq
    3ad2ant3
    @22
    cA
    cB
    qdivcl
    syl3anc
    eqeltrd
    @19
    @23
    @4
    cq
    @18
    cD
    csqrt
    fveq2
    eleq1d
    syl5ibcom
    sylbird
    sylbid
    necon3bd
    imp
end
