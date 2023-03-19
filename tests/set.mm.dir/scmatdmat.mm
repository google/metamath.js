include "cfn.mm"
include "wcel.mm"
include "crg.mm"
include "wa.mm"
include "wss.mm"
include "cv.mm"
include "co.mm"
include "wceq.mm"
include "cif.mm"
include "wral.mm"
include "wrex.mm"
include "crab.mm"
include "wne.mm"
include "wi.mm"
include "id.mm"
include "ifnefalse.mm"
include "sylan9eq.mm"
include "ex.mm"
include "a1i.mm"
include "ralimdva.mm"
include "rexlimdva.mm"
include "ss2rabdv.mm"
include "adantr.mm"
include "wb.mm"
include "scmatmats.mm"
include "dmatval.mm"
include "sseq12d.mm"
include "mpbird.mm"
include "simpr.mm"
include "sseldd.mm"

theorem scmatdmat
  let cA: class A
  let cB: class B
  let cD: class D
  let cR: class R
  let cS: class S
  let cE: class E
  let cM: class M
  let cN: class N
  let c.0: class .0.
  let vi: setvar i
  let vj: setvar j
  let vc: setvar c
  let vm: setvar m
  assume scmatid.a: |- A = ( N Mat R )
  assume scmatid.b: |- B = ( Base ` A )
  assume scmatid.e: |- E = ( Base ` R )
  assume scmatid.0: |- .0. = ( 0g ` R )
  assume scmatid.s: |- S = ( N ScMat R )
  assume scmatdmat.d: |- D = ( N DMat R )


  assert |- ( ( N e. Fin /\ R e. Ring ) -> ( M e. S -> M e. D ) )

  proof
    cN
    cfn
    wcel
    cR
    crg
    wcel
    wa
    #
    cM
    cS
    wcel
    #
    cM
    cD
    wcel
    @0
    @1
    wa
    #
    cS
    cD
    cM
    @2
    cS
    cD
    wss
    #
    vi
    cv
    #
    vj
    cv
    #
    vm
    cv
    #
    co
    #
    @4
    @5
    wceq
    vc
    cv
    #
    c.0
    cif
    #
    wceq
    #
    vj
    cN
    wral
    #
    vi
    cN
    wral
    #
    vc
    cE
    wrex
    #
    vm
    cB
    crab
    #
    @4
    @5
    wne
    #
    @7
    c.0
    wceq
    #
    wi
    #
    vj
    cN
    wral
    #
    vi
    cN
    wral
    #
    vm
    cB
    crab
    #
    wss
    #
    @0
    @21
    @1
    @0
    @13
    @19
    vm
    cB
    @0
    @6
    cB
    wcel
    wa
    #
    @12
    @19
    vc
    cE
    @22
    @8
    cE
    wcel
    wa
    #
    @11
    @18
    vi
    cN
    @23
    @4
    cN
    wcel
    wa
    #
    @10
    @17
    vj
    cN
    @10
    @17
    wi
    @24
    @5
    cN
    wcel
    wa
    @10
    @15
    @16
    @10
    @15
    @7
    @9
    c.0
    @10
    id
    @4
    @5
    @8
    c.0
    ifnefalse
    sylan9eq
    ex
    a1i
    ralimdva
    ralimdva
    rexlimdva
    ss2rabdv
    adantr
    @0
    @3
    @21
    wb
    @1
    @0
    cS
    @14
    cD
    @20
    cA
    cB
    cR
    cS
    vi
    vj
    vm
    cE
    cN
    c.0
    vc
    scmatid.a
    scmatid.b
    scmatid.s
    scmatid.e
    scmatid.0
    scmatmats
    cA
    cB
    cD
    cR
    vi
    vj
    vm
    cN
    crg
    c.0
    scmatid.a
    scmatid.b
    scmatid.0
    scmatdmat.d
    dmatval
    sseq12d
    adantr
    mpbird
    @0
    @1
    simpr
    sseldd
    ex
end
