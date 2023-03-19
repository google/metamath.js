include "cr.mm"
include "wss.mm"
include "cn.mm"
include "cdom.mm"
include "wbr.mm"
include "wa.mm"
include "cpw.mm"
include "wn.mm"
include "cioo.mm"
include "crn.mm"
include "ctg.mm"
include "cfv.mm"
include "cnt.mm"
include "c0.mm"
include "wceq.mm"
include "csdm.mm"
include "nnex.mm"
include "canth2.mm"
include "domnsym.mm"
include "mt2.mm"
include "wne.mm"
include "cen.mm"
include "wcel.mm"
include "wi.mm"
include "ctop.mm"
include "retop.mm"
include "simpl.mm"
include "uniretop.mm"
include "ntropn.mm"
include "sylancr.mm"
include "opnreen.mm"
include "ex.mm"
include "syl.mm"
include "cvv.mm"
include "reex.mm"
include "ssex.mm"
include "ntrss2.mm"
include "mpan.mm"
include "ssdomg.mm"
include "sylc.mm"
include "domtr.mm"
include "sylan.mm"
include "ensym.mm"
include "endomtr.mm"
include "expcom.mm"
include "syl2im.mm"
include "syld.mm"
include "necon1bd.mm"
include "mpi.mm"

theorem rectbntr0
  let cA: class A


  assert |- ( ( A C_ RR /\ A ~<_ NN ) -> ( ( int ` ( topGen ` ran (,) ) ) ` A ) = (/) )

  proof
    cA
    cr
    wss
    #
    cA
    cn
    cdom
    wbr
    #
    wa
    #
    cn
    cpw
    #
    cn
    cdom
    wbr
    #
    wn
    cA
    cioo
    crn
    ctg
    cfv
    #
    cnt
    cfv
    cfv
    #
    c0
    wceq
    @4
    cn
    @3
    csdm
    wbr
    cn
    nnex
    canth2
    @3
    cn
    domnsym
    mt2
    @2
    @4
    @6
    c0
    @2
    @6
    c0
    wne
    #
    @6
    @3
    cen
    wbr
    #
    @4
    @2
    @6
    @5
    wcel
    #
    @7
    @8
    wi
    @2
    @5
    ctop
    wcel
    #
    @0
    @9
    retop
    @0
    @1
    simpl
    cA
    @5
    cr
    uniretop
    ntropn
    sylancr
    @9
    @7
    @8
    @6
    opnreen
    ex
    syl
    @2
    @6
    cn
    cdom
    wbr
    #
    @8
    @3
    @6
    cen
    wbr
    #
    @4
    @0
    @6
    cA
    cdom
    wbr
    #
    @1
    @11
    @0
    cA
    cvv
    wcel
    @6
    cA
    wss
    #
    @13
    cA
    cr
    reex
    ssex
    @10
    @0
    @14
    retop
    cA
    @5
    cr
    uniretop
    ntrss2
    mpan
    @6
    cA
    cvv
    ssdomg
    sylc
    @6
    cA
    cn
    domtr
    sylan
    @6
    @3
    ensym
    @12
    @11
    @4
    @3
    @6
    cn
    endomtr
    expcom
    syl2im
    syld
    necon1bd
    mpi
end
