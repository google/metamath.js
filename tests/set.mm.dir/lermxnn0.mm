include "c2.mm"
include "cuz.mm"
include "cfv.mm"
include "wcel.mm"
include "cn0.mm"
include "cle.mm"
include "wbr.mm"
include "crmx.mm"
include "co.mm"
include "wb.mm"
include "cv.mm"
include "oveq2.mm"
include "nn0ssre.mm"
include "wa.mm"
include "cz.mm"
include "nn0z.mm"
include "frmx.mm"
include "fovcl.mm"
include "sylan2.mm"
include "nn0red.mm"
include "clt.mm"
include "wi.mm"
include "w3a.mm"
include "ltrmxnn0.mm"
include "biimpd.mm"
include "3expb.mm"
include "leord1.mm"
include "3impb.mm"

theorem lermxnn0
  let cA: class A
  let cM: class M
  let cN: class N
  let va: setvar a
  let vb: setvar b


  assert |- ( ( A e. ( ZZ>= ` 2 ) /\ M e. NN0 /\ N e. NN0 ) -> ( M <_ N <-> ( A rmX M ) <_ ( A rmX N ) ) )

  proof
    cA
    c2
    cuz
    cfv
    #
    wcel
    #
    cM
    cn0
    wcel
    cN
    cn0
    wcel
    cM
    cN
    cle
    wbr
    cA
    cM
    crmx
    co
    #
    cA
    cN
    crmx
    co
    #
    cle
    wbr
    wb
    @1
    va
    vb
    cA
    va
    cv
    #
    crmx
    co
    #
    cA
    vb
    cv
    #
    crmx
    co
    #
    cM
    cN
    cn0
    @2
    @3
    @4
    @6
    cA
    crmx
    oveq2
    @4
    cM
    cA
    crmx
    oveq2
    @4
    cN
    cA
    crmx
    oveq2
    nn0ssre
    @1
    @4
    cn0
    wcel
    #
    wa
    @5
    @8
    @1
    @4
    cz
    wcel
    @5
    cn0
    wcel
    @4
    nn0z
    cA
    @4
    cn0
    @0
    cz
    crmx
    frmx
    fovcl
    sylan2
    nn0red
    @1
    @8
    @6
    cn0
    wcel
    #
    @4
    @6
    clt
    wbr
    #
    @5
    @7
    clt
    wbr
    #
    wi
    @1
    @8
    @9
    w3a
    @10
    @11
    cA
    @4
    @6
    ltrmxnn0
    biimpd
    3expb
    leord1
    3impb
end
