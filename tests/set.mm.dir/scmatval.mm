include "cfn.mm"
include "wcel.mm"
include "wa.mm"
include "cscmat.mm"
include "co.mm"
include "cv.mm"
include "wceq.mm"
include "wrex.mm"
include "crab.mm"
include "cvv.mm"
include "cmat.mm"
include "cur.mm"
include "cfv.mm"
include "cvsca.mm"
include "cbs.mm"
include "csb.mm"
include "cmpt2.mm"
include "df-scmat.mm"
include "a1i.mm"
include "ovexd.mm"
include "fveq2.mm"
include "eqidd.mm"
include "oveq123d.mm"
include "eqeq2d.mm"
include "rexbidv.mm"
include "rabeqbidv.mm"
include "adantl.mm"
include "csbied.mm"
include "oveq12.mm"
include "fveq2d.mm"
include "fveq2i.mm"
include "eqtri.mm"
include "syl6eqr.mm"
include "rexeqbidv.mm"
include "eqtrd.mm"
include "simpl.mm"
include "elex.mm"
include "fvex.mm"
include "eqeltri.mm"
include "rabex.mm"
include "ovmpt2d.mm"
include "syl5eq.mm"

theorem scmatval
  let cA: class A
  let cB: class B
  let cR: class R
  let cS: class S
  let c.x: class .x.
  let c.1: class .1.
  let vm: setvar m
  let cK: class K
  let cN: class N
  let cV: class V
  let vc: setvar c
  let vn: setvar n
  let vr: setvar r
  let va: setvar a
  assume scmatval.k: |- K = ( Base ` R )
  assume scmatval.a: |- A = ( N Mat R )
  assume scmatval.b: |- B = ( Base ` A )
  assume scmatval.1: |- .1. = ( 1r ` A )
  assume scmatval.t: |- .x. = ( .s ` A )
  assume scmatval.s: |- S = ( N ScMat R )

  disjoint B m
  disjoint K c
  disjoint N c
  disjoint N m
  disjoint c m
  disjoint R c
  disjoint R m
  disjoint B n
  disjoint B r
  disjoint m n
  disjoint m r
  disjoint n r
  disjoint K n
  disjoint K r
  disjoint c n
  disjoint c r
  disjoint N a
  disjoint N n
  disjoint N r
  disjoint a c
  disjoint a m
  disjoint a n
  disjoint a r
  disjoint R a
  disjoint R n
  disjoint R r
  disjoint V a
  disjoint V n
  disjoint V r
  disjoint .1. n
  disjoint .1. r
  disjoint .x. n
  disjoint .x. r
  assert |- ( ( N e. Fin /\ R e. V ) -> S = { m e. B | E. c e. K m = ( c .x. .1. ) } )

  proof
    cN
    cfn
    wcel
    #
    cR
    cV
    wcel
    #
    wa
    #
    cS
    cN
    cR
    cscmat
    co
    vm
    cv
    #
    vc
    cv
    #
    c.1
    c.x
    co
    #
    wceq
    #
    vc
    cK
    wrex
    #
    vm
    cB
    crab
    #
    scmatval.s
    @2
    vn
    vr
    cN
    cR
    cfn
    cvv
    va
    vn
    cv
    #
    vr
    cv
    #
    cmat
    co
    #
    @3
    @4
    va
    cv
    #
    cur
    cfv
    #
    @12
    cvsca
    cfv
    #
    co
    #
    wceq
    #
    vc
    @10
    cbs
    cfv
    #
    wrex
    #
    vm
    @12
    cbs
    cfv
    #
    crab
    #
    csb
    #
    @8
    cscmat
    cvv
    cscmat
    vn
    vr
    cfn
    cvv
    @21
    cmpt2
    wceq
    @2
    vm
    vn
    vr
    va
    vc
    df-scmat
    a1i
    @2
    @9
    cN
    wceq
    #
    @10
    cR
    wceq
    #
    wa
    #
    wa
    #
    @21
    @3
    @4
    @11
    cur
    cfv
    #
    @11
    cvsca
    cfv
    #
    co
    #
    wceq
    #
    vc
    @17
    wrex
    #
    vm
    @11
    cbs
    cfv
    #
    crab
    #
    @8
    @25
    va
    @11
    @20
    @32
    cvv
    @25
    @9
    @10
    cmat
    ovexd
    @12
    @11
    wceq
    #
    @20
    @32
    wceq
    @25
    @33
    @18
    @30
    vm
    @19
    @31
    @12
    @11
    cbs
    fveq2
    @33
    @16
    @29
    vc
    @17
    @33
    @15
    @28
    @3
    @33
    @4
    @4
    @13
    @26
    @14
    @27
    @12
    @11
    cvsca
    fveq2
    @33
    @4
    eqidd
    @12
    @11
    cur
    fveq2
    oveq123d
    eqeq2d
    rexbidv
    rabeqbidv
    adantl
    csbied
    @24
    @32
    @8
    wceq
    @2
    @24
    @30
    @7
    vm
    @31
    cB
    @24
    @31
    cN
    cR
    cmat
    co
    #
    cbs
    cfv
    #
    cB
    @24
    @11
    @34
    cbs
    @9
    cN
    @10
    cR
    cmat
    oveq12
    #
    fveq2d
    cB
    cA
    cbs
    cfv
    #
    @35
    scmatval.b
    cA
    @34
    cbs
    scmatval.a
    fveq2i
    eqtri
    syl6eqr
    @24
    @29
    @6
    vc
    @17
    cK
    @23
    @17
    cK
    wceq
    @22
    @23
    @17
    cR
    cbs
    cfv
    cK
    @10
    cR
    cbs
    fveq2
    scmatval.k
    syl6eqr
    adantl
    @24
    @28
    @5
    @3
    @24
    @4
    @4
    @26
    c.1
    @27
    c.x
    @24
    @27
    @34
    cvsca
    cfv
    #
    c.x
    @24
    @11
    @34
    cvsca
    @36
    fveq2d
    c.x
    cA
    cvsca
    cfv
    @38
    scmatval.t
    cA
    @34
    cvsca
    scmatval.a
    fveq2i
    eqtri
    syl6eqr
    @24
    @4
    eqidd
    @24
    @26
    @34
    cur
    cfv
    #
    c.1
    @24
    @11
    @34
    cur
    @36
    fveq2d
    c.1
    cA
    cur
    cfv
    @39
    scmatval.1
    cA
    @34
    cur
    scmatval.a
    fveq2i
    eqtri
    syl6eqr
    oveq123d
    eqeq2d
    rexeqbidv
    rabeqbidv
    adantl
    eqtrd
    @0
    @1
    simpl
    @1
    cR
    cvv
    wcel
    @0
    cR
    cV
    elex
    adantl
    @8
    cvv
    wcel
    @2
    @7
    vm
    cB
    cB
    @37
    cvv
    scmatval.b
    cA
    cbs
    fvex
    eqeltri
    rabex
    a1i
    ovmpt2d
    syl5eq
end
