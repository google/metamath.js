include "cvv.mm"
include "wcel.mm"
include "cv.mm"
include "csuc.mm"
include "wceq.mm"
include "wfn.mm"
include "wa.mm"
include "wi.mm"
include "c0.mm"
include "cif.mm"
include "cop.mm"
include "csn.mm"
include "cun.mm"
include "opeq2.mm"
include "sneqd.mm"
include "uneq2d.mm"
include "syl5eq.mm"
include "fneq1d.mm"
include "imbi2d.mm"
include "eqid.mm"
include "0ex.mm"
include "elimel.mm"
include "bnj927.mm"
include "dedth.mm"

theorem bnj941
  let cC: class C
  let vf: setvar f
  let vn: setvar n
  let cG: class G
  let vp: setvar p
  assume bnj941.1: |- G = ( f u. { <. n , C >. } )


  assert |- ( C e. _V -> ( ( p = suc n /\ f Fn n ) -> G Fn p ) )

  proof
    cC
    cvv
    wcel
    #
    vp
    cv
    #
    vn
    cv
    #
    csuc
    wceq
    vf
    cv
    #
    @2
    wfn
    wa
    #
    cG
    @1
    wfn
    #
    wi
    @4
    @3
    @2
    @0
    cC
    c0
    cif
    #
    cop
    #
    csn
    #
    cun
    #
    @1
    wfn
    #
    wi
    cC
    c0
    cC
    @6
    wceq
    #
    @5
    @10
    @4
    @11
    @1
    cG
    @9
    @11
    cG
    @3
    @2
    cC
    cop
    #
    csn
    #
    cun
    @9
    bnj941.1
    @11
    @13
    @8
    @3
    @11
    @12
    @7
    cC
    @6
    @2
    opeq2
    sneqd
    uneq2d
    syl5eq
    fneq1d
    imbi2d
    @6
    vf
    vn
    @9
    vp
    @9
    eqid
    cC
    c0
    cvv
    0ex
    elimel
    bnj927
    dedth
end
