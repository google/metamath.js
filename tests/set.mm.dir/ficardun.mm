include "cfn.mm"
include "wcel.mm"
include "cin.mm"
include "c0.mm"
include "wceq.mm"
include "w3a.mm"
include "ccrd.mm"
include "cfv.mm"
include "coa.mm"
include "co.mm"
include "cun.mm"
include "cen.mm"
include "wbr.mm"
include "ccda.mm"
include "cdm.mm"
include "finnum.mm"
include "cardacda.mm"
include "syl2an.mm"
include "3adant3.mm"
include "ensymd.mm"
include "cdaun.mm"
include "entr.mm"
include "syl2anc.mm"
include "carden2b.mm"
include "syl.mm"
include "com.mm"
include "ficardom.mm"
include "wa.mm"
include "nnacl.mm"
include "cardnn.mm"
include "eqtr3d.mm"

theorem ficardun
  let cA: class A
  let cB: class B


  assert |- ( ( A e. Fin /\ B e. Fin /\ ( A i^i B ) = (/) ) -> ( card ` ( A u. B ) ) = ( ( card ` A ) +o ( card ` B ) ) )

  proof
    cA
    cfn
    wcel
    #
    cB
    cfn
    wcel
    #
    cA
    cB
    cin
    c0
    wceq
    #
    w3a
    #
    cA
    ccrd
    cfv
    #
    cB
    ccrd
    cfv
    #
    coa
    co
    #
    ccrd
    cfv
    #
    cA
    cB
    cun
    #
    ccrd
    cfv
    #
    @6
    @3
    @6
    @8
    cen
    wbr
    #
    @7
    @9
    wceq
    @3
    @6
    cA
    cB
    ccda
    co
    #
    cen
    wbr
    @11
    @8
    cen
    wbr
    @10
    @3
    @11
    @6
    @0
    @1
    @11
    @6
    cen
    wbr
    #
    @2
    @0
    cA
    ccrd
    cdm
    #
    wcel
    cB
    @13
    wcel
    @12
    @1
    cA
    finnum
    cB
    finnum
    cA
    cB
    cardacda
    syl2an
    3adant3
    ensymd
    cA
    cB
    cfn
    cfn
    cdaun
    @6
    @11
    @8
    entr
    syl2anc
    @6
    @8
    carden2b
    syl
    @0
    @1
    @7
    @6
    wceq
    #
    @2
    @0
    @4
    com
    wcel
    #
    @5
    com
    wcel
    #
    @14
    @1
    cA
    ficardom
    cB
    ficardom
    @15
    @16
    wa
    @6
    com
    wcel
    @14
    @4
    @5
    nnacl
    @6
    cardnn
    syl
    syl2an
    3adant3
    eqtr3d
end
