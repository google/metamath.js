include "c2.mm"
include "cuz.mm"
include "cfv.mm"
include "wcel.mm"
include "cz.mm"
include "wa.mm"
include "cn0.mm"
include "crmx.mm"
include "co.mm"
include "cn.mm"
include "cneg.mm"
include "cc0.mm"
include "clt.mm"
include "wbr.mm"
include "nn0z.mm"
include "frmx.mm"
include "fovcl.mm"
include "sylan2.mm"
include "crmy.mm"
include "cle.mm"
include "rmxypos.mm"
include "simpld.mm"
include "elnnnn0b.mm"
include "sylanbrc.mm"
include "adantlr.mm"
include "wceq.mm"
include "rmxneg.mm"
include "adantr.mm"
include "eqeltrrd.mm"
include "wo.mm"
include "cr.mm"
include "elznn0.mm"
include "simprbi.mm"
include "adantl.mm"
include "mpjaodan.mm"

theorem rmxnn
  let cA: class A
  let cN: class N
  let va: setvar a
  let vb: setvar b
  let cM: class M


  assert |- ( ( A e. ( ZZ>= ` 2 ) /\ N e. ZZ ) -> ( A rmX N ) e. NN )

  proof
    cA
    c2
    cuz
    cfv
    #
    wcel
    #
    cN
    cz
    wcel
    #
    wa
    #
    cN
    cn0
    wcel
    #
    cA
    cN
    crmx
    co
    #
    cn
    wcel
    #
    cN
    cneg
    #
    cn0
    wcel
    #
    @1
    @4
    @6
    @2
    @1
    @4
    wa
    #
    @5
    cn0
    wcel
    #
    cc0
    @5
    clt
    wbr
    #
    @6
    @4
    @1
    @2
    @10
    cN
    nn0z
    cA
    cN
    cn0
    @0
    cz
    crmx
    frmx
    fovcl
    sylan2
    @9
    @11
    cc0
    cA
    cN
    crmy
    co
    cle
    wbr
    cA
    cN
    rmxypos
    simpld
    @5
    elnnnn0b
    sylanbrc
    adantlr
    @3
    @8
    wa
    cA
    @7
    crmx
    co
    #
    @5
    cn
    @3
    @12
    @5
    wceq
    @8
    cA
    cN
    rmxneg
    adantr
    @1
    @8
    @12
    cn
    wcel
    #
    @2
    @1
    @8
    wa
    #
    @12
    cn0
    wcel
    #
    cc0
    @12
    clt
    wbr
    #
    @13
    @8
    @1
    @7
    cz
    wcel
    @15
    @7
    nn0z
    cA
    @7
    cn0
    @0
    cz
    crmx
    frmx
    fovcl
    sylan2
    @14
    @16
    cc0
    cA
    @7
    crmy
    co
    cle
    wbr
    cA
    @7
    rmxypos
    simpld
    @12
    elnnnn0b
    sylanbrc
    adantlr
    eqeltrrd
    @2
    @4
    @8
    wo
    #
    @1
    @2
    cN
    cr
    wcel
    @17
    cN
    elznn0
    simprbi
    adantl
    mpjaodan
end
