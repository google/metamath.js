include "cch.mm"
include "wcel.mm"
include "chil.mm"
include "wa.mm"
include "cpjh.mm"
include "cfv.mm"
include "cno.mm"
include "wceq.mm"
include "cle.mm"
include "wbr.mm"
include "clt.mm"
include "wn.mm"
include "cr.mm"
include "pjhcl.mm"
include "normcl.mm"
include "syl.mm"
include "adantl.mm"
include "eqleltd.mm"
include "pjnorm.mm"
include "biantrurd.mm"
include "pjnel.mm"
include "con1bid.mm"
include "3bitr2rd.mm"

theorem pjnorm2
  let cA: class A
  let cH: class H


  assert |- ( ( H e. CH /\ A e. ~H ) -> ( A e. H <-> ( normh ` ( ( projh ` H ) ` A ) ) = ( normh ` A ) ) )

  proof
    cH
    cch
    wcel
    #
    cA
    chil
    wcel
    #
    wa
    #
    cA
    cH
    cpjh
    cfv
    cfv
    #
    cno
    cfv
    #
    cA
    cno
    cfv
    #
    wceq
    @4
    @5
    cle
    wbr
    #
    @4
    @5
    clt
    wbr
    #
    wn
    #
    wa
    @8
    cA
    cH
    wcel
    #
    @2
    @4
    @5
    @2
    @3
    chil
    wcel
    @4
    cr
    wcel
    cA
    cH
    pjhcl
    @3
    normcl
    syl
    @1
    @5
    cr
    wcel
    @0
    cA
    normcl
    adantl
    eqleltd
    @2
    @6
    @8
    cA
    cH
    pjnorm
    biantrurd
    @2
    @9
    @7
    cA
    cH
    pjnel
    con1bid
    3bitr2rd
end
