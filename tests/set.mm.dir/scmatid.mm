include "cfn.mm"
include "wcel.mm"
include "crg.mm"
include "wa.mm"
include "cur.mm"
include "cfv.mm"
include "cv.mm"
include "cvsca.mm"
include "co.mm"
include "wceq.mm"
include "cbs.mm"
include "wrex.mm"
include "matring.mm"
include "eqid.mm"
include "ringidcl.mm"
include "syl.mm"
include "csca.mm"
include "matsca2.mm"
include "eqcomd.mm"
include "fveq2d.mm"
include "adantl.mm"
include "eqeltrd.mm"
include "wb.mm"
include "oveq1.mm"
include "eqeq2d.mm"
include "clmod.mm"
include "matlmod.mm"
include "lmodvs1.mm"
include "syl2anc.mm"
include "rspcedvd.mm"
include "scmatel.mm"
include "mpbir2and.mm"

theorem scmatid
  let cA: class A
  let cB: class B
  let cR: class R
  let cS: class S
  let cE: class E
  let cN: class N
  let c.0: class .0.
  let vc: setvar c
  assume scmatid.a: |- A = ( N Mat R )
  assume scmatid.b: |- B = ( Base ` A )
  assume scmatid.e: |- E = ( Base ` R )
  assume scmatid.0: |- .0. = ( 0g ` R )
  assume scmatid.s: |- S = ( N ScMat R )


  assert |- ( ( N e. Fin /\ R e. Ring ) -> ( 1r ` A ) e. S )

  proof
    cN
    cfn
    wcel
    #
    cR
    crg
    wcel
    #
    wa
    #
    cA
    cur
    cfv
    #
    cS
    wcel
    @3
    cB
    wcel
    #
    @3
    vc
    cv
    #
    @3
    cA
    cvsca
    cfv
    #
    co
    #
    wceq
    #
    vc
    cR
    cbs
    cfv
    #
    wrex
    @2
    cA
    crg
    wcel
    @4
    cA
    cR
    cN
    scmatid.a
    matring
    cB
    cA
    @3
    scmatid.b
    @3
    eqid
    #
    ringidcl
    syl
    #
    @2
    @8
    @3
    cA
    csca
    cfv
    #
    cur
    cfv
    #
    @3
    @6
    co
    #
    wceq
    #
    vc
    @13
    @9
    @2
    @13
    cR
    cur
    cfv
    #
    @9
    @2
    @12
    cR
    cur
    @2
    cR
    @12
    cA
    cR
    cN
    crg
    scmatid.a
    matsca2
    eqcomd
    fveq2d
    @1
    @16
    @9
    wcel
    @0
    @9
    cR
    @16
    @9
    eqid
    #
    @16
    eqid
    ringidcl
    adantl
    eqeltrd
    @5
    @13
    wceq
    #
    @8
    @15
    wb
    @2
    @18
    @7
    @14
    @3
    @5
    @13
    @3
    @6
    oveq1
    eqeq2d
    adantl
    @2
    @14
    @3
    @2
    cA
    clmod
    wcel
    @4
    @14
    @3
    wceq
    cA
    cR
    cN
    scmatid.a
    matlmod
    @11
    @6
    @13
    @12
    cB
    cA
    @3
    scmatid.b
    @12
    eqid
    @6
    eqid
    #
    @13
    eqid
    lmodvs1
    syl2anc
    eqcomd
    rspcedvd
    cA
    cB
    cR
    cS
    @6
    @3
    @9
    @3
    cN
    crg
    vc
    @17
    scmatid.a
    scmatid.b
    @10
    @19
    scmatid.s
    scmatel
    mpbir2and
end
