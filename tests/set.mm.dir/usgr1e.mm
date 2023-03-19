include "cuspgr.mm"
include "wcel.mm"
include "cv.mm"
include "chash.mm"
include "cfv.mm"
include "c2.mm"
include "wceq.mm"
include "cedg.mm"
include "wral.mm"
include "cusgr.mm"
include "uspgr1e.mm"
include "cpr.mm"
include "csn.mm"
include "wne.mm"
include "wb.mm"
include "hashprg.mm"
include "syl2anc.mm"
include "mpbid.mm"
include "prex.mm"
include "fveq2.mm"
include "eqeq1d.mm"
include "ralsn.mm"
include "sylibr.mm"
include "ciedg.mm"
include "crn.mm"
include "cop.mm"
include "edgval.mm"
include "a1i.mm"
include "rneqd.mm"
include "rnsnopg.mm"
include "syl.mm"
include "3eqtrd.mm"
include "raleqdv.mm"
include "mpbird.mm"
include "usgruspgrb.mm"
include "sylanbrc.mm"

theorem usgr1e
  let wph: wff ph
  let cA: class A
  let cB: class B
  let cC: class C
  let cG: class G
  let cV: class V
  let cX: class X
  let vx: setvar x
  assume uspgr1e.v: |- V = ( Vtx ` G )
  assume uspgr1e.a: |- ( ph -> A e. X )
  assume uspgr1e.b: |- ( ph -> B e. V )
  assume uspgr1e.c: |- ( ph -> C e. V )
  assume uspgr1e.e: |- ( ph -> ( iEdg ` G ) = { <. A , { B , C } >. } )
  assume usgr1e.e: |- ( ph -> B =/= C )


  assert |- ( ph -> G e. USGraph )

  proof
    wph
    cG
    cuspgr
    wcel
    vx
    cv
    #
    chash
    cfv
    #
    c2
    wceq
    #
    vx
    cG
    cedg
    cfv
    #
    wral
    #
    cG
    cusgr
    wcel
    wph
    cA
    cB
    cC
    cG
    cV
    cX
    uspgr1e.v
    uspgr1e.a
    uspgr1e.b
    uspgr1e.c
    uspgr1e.e
    uspgr1e
    wph
    @4
    @2
    vx
    cB
    cC
    cpr
    #
    csn
    #
    wral
    #
    wph
    @5
    chash
    cfv
    #
    c2
    wceq
    #
    @7
    wph
    cB
    cC
    wne
    #
    @9
    usgr1e.e
    wph
    cB
    cV
    wcel
    cC
    cV
    wcel
    @10
    @9
    wb
    uspgr1e.b
    uspgr1e.c
    cB
    cC
    cV
    cV
    hashprg
    syl2anc
    mpbid
    @2
    @9
    vx
    @5
    cB
    cC
    prex
    @0
    @5
    wceq
    @1
    @8
    c2
    @0
    @5
    chash
    fveq2
    eqeq1d
    ralsn
    sylibr
    wph
    @2
    vx
    @3
    @6
    wph
    @3
    cG
    ciedg
    cfv
    #
    crn
    #
    cA
    @5
    cop
    csn
    #
    crn
    #
    @6
    @3
    @12
    wceq
    wph
    cG
    edgval
    a1i
    wph
    @11
    @13
    uspgr1e.e
    rneqd
    wph
    cA
    cX
    wcel
    @14
    @6
    wceq
    uspgr1e.a
    cA
    @5
    cX
    rnsnopg
    syl
    3eqtrd
    raleqdv
    mpbird
    vx
    cG
    usgruspgrb
    sylanbrc
end
