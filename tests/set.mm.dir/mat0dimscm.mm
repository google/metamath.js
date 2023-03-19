include "crg.mm"
include "wcel.mm"
include "cbs.mm"
include "cfv.mm"
include "wa.mm"
include "c0.mm"
include "cvsca.mm"
include "co.mm"
include "wceq.mm"
include "simpl.mm"
include "clmod.mm"
include "csca.mm"
include "cfn.mm"
include "0fin.mm"
include "matlmod.mm"
include "sylancr.mm"
include "matsca2.mm"
include "mpan.mm"
include "fveq2d.mm"
include "eleq2d.mm"
include "biimpa.mm"
include "csn.mm"
include "0ex.mm"
include "snid.mm"
include "cmat.mm"
include "fveq2i.mm"
include "mat0dimbas0.mm"
include "syl5eq.mm"
include "syl5eleqr.mm"
include "adantr.mm"
include "eqid.mm"
include "lmodvscl.mm"
include "syl3anc.mm"
include "elsni.mm"
include "syl6bi.mm"
include "sylc.mm"

theorem mat0dimscm
  let cA: class A
  let cR: class R
  let cX: class X
  assume mat0dim.a: |- A = ( (/) Mat R )


  assert |- ( ( R e. Ring /\ X e. ( Base ` R ) ) -> ( X ( .s ` A ) (/) ) = (/) )

  proof
    cR
    crg
    wcel
    #
    cX
    cR
    cbs
    cfv
    #
    wcel
    #
    wa
    #
    @0
    cX
    c0
    cA
    cvsca
    cfv
    #
    co
    #
    cA
    cbs
    cfv
    #
    wcel
    #
    @5
    c0
    wceq
    #
    @0
    @2
    simpl
    #
    @3
    cA
    clmod
    wcel
    #
    cX
    cA
    csca
    cfv
    #
    cbs
    cfv
    #
    wcel
    #
    c0
    @6
    wcel
    #
    @7
    @3
    c0
    cfn
    wcel
    #
    @0
    @10
    0fin
    @9
    cA
    cR
    c0
    mat0dim.a
    matlmod
    sylancr
    @0
    @2
    @13
    @0
    @1
    @12
    cX
    @0
    cR
    @11
    cbs
    @15
    @0
    cR
    @11
    wceq
    0fin
    cA
    cR
    c0
    crg
    mat0dim.a
    matsca2
    mpan
    fveq2d
    eleq2d
    biimpa
    @0
    @14
    @2
    @0
    c0
    c0
    csn
    #
    @6
    c0
    0ex
    snid
    @0
    @6
    c0
    cR
    cmat
    co
    #
    cbs
    cfv
    @16
    cA
    @17
    cbs
    mat0dim.a
    fveq2i
    cR
    crg
    mat0dimbas0
    syl5eq
    #
    syl5eleqr
    adantr
    cX
    @4
    @11
    @12
    @6
    cA
    c0
    @6
    eqid
    @11
    eqid
    @4
    eqid
    @12
    eqid
    lmodvscl
    syl3anc
    @0
    @7
    @5
    @16
    wcel
    @8
    @0
    @6
    @16
    @5
    @18
    eleq2d
    @5
    c0
    elsni
    syl6bi
    sylc
end
