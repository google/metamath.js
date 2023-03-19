include "crg.mm"
include "wcel.mm"
include "cur.mm"
include "cfv.mm"
include "cbs.mm"
include "c0.mm"
include "wceq.mm"
include "cfn.mm"
include "0fin.mm"
include "matring.mm"
include "mpan.mm"
include "eqid.mm"
include "ringidcl.mm"
include "syl.mm"
include "csn.mm"
include "cmat.mm"
include "co.mm"
include "fveq2i.mm"
include "mat0dimbas0.mm"
include "syl5eq.mm"
include "eleq2d.mm"
include "elsni.mm"
include "syl6bi.mm"
include "mpd.mm"

theorem mat0dimid
  let cA: class A
  let cR: class R
  assume mat0dim.a: |- A = ( (/) Mat R )


  assert |- ( R e. Ring -> ( 1r ` A ) = (/) )

  proof
    cR
    crg
    wcel
    #
    cA
    cur
    cfv
    #
    cA
    cbs
    cfv
    #
    wcel
    #
    @1
    c0
    wceq
    #
    @0
    cA
    crg
    wcel
    #
    @3
    c0
    cfn
    wcel
    @0
    @5
    0fin
    cA
    cR
    c0
    mat0dim.a
    matring
    mpan
    @2
    cA
    @1
    @2
    eqid
    @1
    eqid
    ringidcl
    syl
    @0
    @3
    @1
    c0
    csn
    #
    wcel
    @4
    @0
    @2
    @6
    @1
    @0
    @2
    c0
    cR
    cmat
    co
    #
    cbs
    cfv
    @6
    cA
    @7
    cbs
    mat0dim.a
    fveq2i
    cR
    crg
    mat0dimbas0
    syl5eq
    eleq2d
    @1
    c0
    elsni
    syl6bi
    mpd
end
