include "cr.mm"
include "wcel.mm"
include "ceu.mm"
include "cle.mm"
include "wbr.mm"
include "wa.mm"
include "clt.mm"
include "wn.mm"
include "clog.mm"
include "cfv.mm"
include "cdiv.mm"
include "co.mm"
include "wb.mm"
include "logdivlt.mm"
include "ancoms.mm"
include "notbid.mm"
include "simpll.mm"
include "simprl.mm"
include "lenltd.mm"
include "crp.mm"
include "cc0.mm"
include "0red.mm"
include "ere.mm"
include "a1i.mm"
include "epos.mm"
include "simprr.mm"
include "ltletrd.mm"
include "elrpd.mm"
include "relogcl.mm"
include "syl.mm"
include "rerpdivcld.mm"
include "simplr.mm"
include "3bitr4d.mm"

theorem logdivle
  let cA: class A
  let cB: class B


  assert |- ( ( ( A e. RR /\ _e <_ A ) /\ ( B e. RR /\ _e <_ B ) ) -> ( A <_ B <-> ( ( log ` B ) / B ) <_ ( ( log ` A ) / A ) ) )

  proof
    cA
    cr
    wcel
    #
    ceu
    cA
    cle
    wbr
    #
    wa
    #
    cB
    cr
    wcel
    #
    ceu
    cB
    cle
    wbr
    #
    wa
    #
    wa
    #
    cB
    cA
    clt
    wbr
    #
    wn
    cA
    clog
    cfv
    #
    cA
    cdiv
    co
    #
    cB
    clog
    cfv
    #
    cB
    cdiv
    co
    #
    clt
    wbr
    #
    wn
    cA
    cB
    cle
    wbr
    @11
    @9
    cle
    wbr
    @6
    @7
    @12
    @5
    @2
    @7
    @12
    wb
    cB
    cA
    logdivlt
    ancoms
    notbid
    @6
    cA
    cB
    @0
    @1
    @5
    simpll
    #
    @2
    @3
    @4
    simprl
    #
    lenltd
    @6
    @11
    @9
    @6
    @10
    cB
    @6
    cB
    crp
    wcel
    @10
    cr
    wcel
    @6
    cB
    @14
    @6
    cc0
    ceu
    cB
    @6
    0red
    #
    ceu
    cr
    wcel
    @6
    ere
    a1i
    #
    @14
    cc0
    ceu
    clt
    wbr
    @6
    epos
    a1i
    #
    @2
    @3
    @4
    simprr
    ltletrd
    elrpd
    #
    cB
    relogcl
    syl
    @18
    rerpdivcld
    @6
    @8
    cA
    @6
    cA
    crp
    wcel
    @8
    cr
    wcel
    @6
    cA
    @13
    @6
    cc0
    ceu
    cA
    @15
    @16
    @13
    @17
    @0
    @1
    @5
    simplr
    ltletrd
    elrpd
    #
    cA
    relogcl
    syl
    @19
    rerpdivcld
    lenltd
    3bitr4d
end
